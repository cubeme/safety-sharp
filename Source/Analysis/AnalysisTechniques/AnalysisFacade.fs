// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

namespace SafetySharp.AnalysisTechniques

open SafetySharp.Workflow
open SafetySharp.Models
open SafetySharp.Models.ScmVerificationElements

// allows caching of analysis techniques to reduce lots of recalculations
//TODO: Refactor Cache, such that it is reusable in several Analysis Techniques at the same time
type private LoadedModelCache = {
    LoadedModel:Scm.ScmModel;
    PropositionalExprParser : string -> ScmVerificationElements.PropositionalExpr;
    LtlExprParser : string -> ScmVerificationElements.LtlExpr;
    CompPathParser : string -> Scm.CompPath;
    // Lazy instantiated Analysis techniques. They are only instantiated, when needed
    LazyAtLtlFormulas : Lazy<AtLtlFormula.AnalyseLtlFormulas>;
    LazyAtDccaLtl : Map<ScmVerificationElements.PropositionalExpr,AtDccaLtl.PerformDccaWithLtlFormulas> ref; //Hazard to At
    LazyAtDccaPruning : Map<ScmVerificationElements.PropositionalExpr,AtDccaPruning.PerformDccaByPruningModels> ref; //Hazard to At
}
    with
        static member initial (scmModel: Scm.ScmModel ) =
            let initialParserState = SafetySharp.Models.ScmVeParser.UserState.initialUserState scmModel
            {
                LoadedModelCache.LoadedModel=scmModel;
                LoadedModelCache.PropositionalExprParser = SafetySharp.Models.ScmVeParser.propositionalExprParser_Result initialParserState;
                LoadedModelCache.LtlExprParser = SafetySharp.Models.ScmVeParser.ltlExprParser_Result initialParserState;
                LoadedModelCache.CompPathParser = SafetySharp.Models.ScmVeParser.locCompInst_Result initialParserState;
                LoadedModelCache.LazyAtLtlFormulas = lazy (new AtLtlFormula.AnalyseLtlFormulas());
                LoadedModelCache.LazyAtDccaLtl = ref Map.empty<ScmVerificationElements.PropositionalExpr,AtDccaLtl.PerformDccaWithLtlFormulas>;
                LoadedModelCache.LazyAtDccaPruning = ref Map.empty<ScmVerificationElements.PropositionalExpr,AtDccaPruning.PerformDccaByPruningModels>;
            }
        member this.AtLtlFormulas = this.LazyAtLtlFormulas.Force()
        member this.AtDccaLtl (hazard) =
            if this.LazyAtDccaLtl.Value.ContainsKey hazard then
                this.LazyAtDccaLtl.Value.Item hazard
            else
                let newAt = AtDccaLtl.PerformDccaWithLtlFormulas(this.LoadedModel,hazard)
                do this.LazyAtDccaLtl := this.LazyAtDccaLtl.Value.Add (hazard,newAt)
                newAt
        member this.AtDccaPruning (hazard) =
            if this.LazyAtDccaPruning.Value.ContainsKey hazard then
                this.LazyAtDccaPruning.Value.Item hazard
            else
                let newAt = AtDccaPruning.PerformDccaByPruningModels(this.LoadedModel,hazard)
                do this.LazyAtDccaPruning := this.LazyAtDccaPruning.Value.Add (hazard,newAt)
                newAt

        //static member resetAnalysisTechniques
        //  TODO: Replaces every instantiated Analysis Technique with an unevaluated "lazy" to allow the garbage
        //  collection of the old instantiated Analysis Techniques

[<RequireQualifiedAccessAttribute>]
type private AnalysisFacadeState =
    | Uninitialized of WorkflowState:WorkflowState<unit>
    | ModelLoaded of LoadedModelCache:LoadedModelCache *
                     WorkflowState:WorkflowState<Scm.ScmModel>
    with
        member this.getLoadedModel : Scm.ScmModel =
            match this with
                | AnalysisFacadeState.Uninitialized (_) ->
                    failwith "Unable to perform action on model because currently no model has been loaded."
                | AnalysisFacadeState.ModelLoaded (currentModelCache,wfState) ->
                    currentModelCache.LoadedModel
        member this.getLoadedModelCache : LoadedModelCache =
            match this with
                | AnalysisFacadeState.Uninitialized (_) ->
                    failwith "Unable to perform action on model because currently no model has been loaded."
                | AnalysisFacadeState.ModelLoaded (currentModelCache,wfState) ->
                    currentModelCache

// Note: Not thread safe
type AnalysisFacade () =
    
    let mutable currentState : AnalysisFacadeState = AnalysisFacadeState.Uninitialized(workflowState_emptyInit ())

    //////// Workflow /////////////

    // Every call may change every content (log/engineoption) of wfState except the inner state. The inner state is always the baseModel
    member private this.RunWorkflowOnModel_getResult<'returnType,'resultingState>
                        (WorkflowFunction s:(WorkflowFunction<Scm.ScmModel,'resultingState,'returnType>))
                        : 'returnType =
        match currentState with
            | AnalysisFacadeState.Uninitialized (_) ->
                failwith "Unable to perform action on model because currently no model has been loaded."
            | AnalysisFacadeState.ModelLoaded (currentModelCache,wfState) ->
                let result,resultingWfState = s wfState
                let resultingWfStateWithCurrentModel =
                    {
                        WorkflowState.State = currentModelCache.LoadedModel;
                        WorkflowState.StepNumber = resultingWfState.StepNumber;
                        WorkflowState.StepName = resultingWfState.StepName;
                        WorkflowState.Log = resultingWfState.Log;
                        WorkflowState.LogEvent = resultingWfState.LogEvent;
                        WorkflowState.EngineOptions = resultingWfState.EngineOptions;
                        WorkflowState.CancellationToken = resultingWfState.CancellationToken;
                        WorkflowState.Tainted = false;
                    }
                currentState <- AnalysisFacadeState.ModelLoaded(currentModelCache,resultingWfStateWithCurrentModel)
                result
                
    // Every call may change every content (log/engineoption) of wfState except the inner state. The inner state is always the baseModel
    member private this.RunWorkflowOnModel_getState<'returnType,'resultingState>
                        (WorkflowFunction s:(WorkflowFunction<Scm.ScmModel,'resultingState,'returnType>))
                        : 'resultingState =
        match currentState with
            | AnalysisFacadeState.Uninitialized (_) ->
                failwith "Unable to perform action on model because currently no model has been loaded."
            | AnalysisFacadeState.ModelLoaded (currentModelCache,wfState) ->
                let result,resultingWfState = s wfState
                let resultingWfStateWithCurrentModel =
                    {
                        WorkflowState.State = currentModelCache.LoadedModel;
                        WorkflowState.StepNumber = resultingWfState.StepNumber;
                        WorkflowState.StepName = resultingWfState.StepName;
                        WorkflowState.Log = resultingWfState.Log;
                        WorkflowState.LogEvent = resultingWfState.LogEvent;
                        WorkflowState.EngineOptions = resultingWfState.EngineOptions;
                        WorkflowState.CancellationToken = resultingWfState.CancellationToken;
                        WorkflowState.Tainted = false;
                    }
                currentState <- AnalysisFacadeState.ModelLoaded(currentModelCache,resultingWfStateWithCurrentModel)
                resultingWfState.State
                                
    //////// Loading Main Model /////////////

    member internal this.setMainModel (_baseModel:Scm.ScmModel) : unit =
        match currentState with
            | AnalysisFacadeState.ModelLoaded (_,wfState) ->
                let newWfState =
                    {
                        WorkflowState.State = _baseModel
                        WorkflowState.StepNumber = wfState.StepNumber;
                        WorkflowState.StepName = wfState.StepName;
                        WorkflowState.Log = wfState.Log;
                        WorkflowState.LogEvent = wfState.LogEvent;
                        WorkflowState.EngineOptions = wfState.EngineOptions;
                        WorkflowState.CancellationToken = wfState.CancellationToken;
                        WorkflowState.Tainted = false;
                    }
                currentState <- AnalysisFacadeState.ModelLoaded(LoadedModelCache.initial _baseModel,newWfState)
                ()
            | AnalysisFacadeState.Uninitialized (wfState) ->
                let newWfState =
                    {
                        WorkflowState.State = _baseModel;
                        WorkflowState.StepNumber = wfState.StepNumber;
                        WorkflowState.StepName = wfState.StepName;
                        WorkflowState.Log = wfState.Log;
                        WorkflowState.LogEvent = wfState.LogEvent;
                        WorkflowState.EngineOptions = wfState.EngineOptions;
                        WorkflowState.CancellationToken = wfState.CancellationToken;
                        WorkflowState.Tainted = false;
                    }
                currentState <- AnalysisFacadeState.ModelLoaded(LoadedModelCache.initial _baseModel,newWfState)
                ()
                
    member internal this.setMainModelFromFile (filename:string) : unit =
        let readFromFileWorkflow (filename:string) = workflow {
            do! readFile filename
            do! SafetySharp.Models.ScmParser.parseStringWorkflow ()
            let! scmTracer = getState ()
            do! updateState (scmTracer.Model)
        }
        match currentState with
            | AnalysisFacadeState.Uninitialized (wfState) ->
                let s = match readFromFileWorkflow filename with | WorkflowFunction(s) -> s
                let _,newWfStateAfterLoading = s wfState
                currentState <- AnalysisFacadeState.ModelLoaded(LoadedModelCache.initial newWfStateAfterLoading.State,newWfStateAfterLoading)
                ()
            | AnalysisFacadeState.ModelLoaded (_,wfState) ->
                let s = match readFromFileWorkflow filename with | WorkflowFunction(s) -> s
                let _,newWfStateAfterLoading = s wfState
                currentState <- AnalysisFacadeState.ModelLoaded(LoadedModelCache.initial newWfStateAfterLoading.State,newWfStateAfterLoading)
                ()
                
    member this.setEmptyMainModel (name:string) : unit =
        let emptyModel = ScmHelpers.createEmptyScmModel (name)
        this.setMainModel (emptyModel)        

    member internal this.injectSamModel (modelToInject:Sam.Pgm, injectIntoPath:Scm.CompPath) : unit =
        let injectIntoModel = currentState.getLoadedModel
        let newModel = InjectSamIntoScm.injectSam injectIntoModel modelToInject injectIntoPath
        this.setMainModel (newModel)

    member this.injectSamModel (modelToInjectFilename:string, injectIntoPath:string) : unit =
        let injectIntoPathParsed = currentState.getLoadedModelCache.CompPathParser injectIntoPath
        let modelToInjectFile = System.IO.File.ReadAllText modelToInjectFilename
        let samModel = SamParser.parseSamFile_Result modelToInjectFile
        this.injectSamModel (samModel,injectIntoPathParsed)
                
    //////// Engine Option /////////////

    member this.setEngineOption (engineOption:SafetySharp.EngineOptions.IEngineOption) : unit =
        // May be set whether a model is loaded or not
        // TODO: Should invalidate the cache
        match currentState with
            | AnalysisFacadeState.Uninitialized (wfState) ->
                let s = match SafetySharp.Workflow.setIEngineOption engineOption with | WorkflowFunction(s) -> s
                let _,newWfState = s wfState
                currentState <- AnalysisFacadeState.Uninitialized(newWfState)
                ()
            | AnalysisFacadeState.ModelLoaded (currentModelCache,wfState) ->
                let s = match SafetySharp.Workflow.setIEngineOption engineOption with | WorkflowFunction(s) -> s
                let _,newWfState = s wfState
                currentState <- AnalysisFacadeState.ModelLoaded(currentModelCache,newWfState)
                ()

    // Analysis Techniques
    
    member internal this.atAnalyseLtl_WithPromela (ltlExpr:LtlExpr) : SafetySharp.Ternary.Ternary =
        let workflowToCalculateLtlResult =
            currentState.getLoadedModelCache.AtLtlFormulas.checkLtlFormulaWithPromela(ltlExpr)
        this.RunWorkflowOnModel_getResult workflowToCalculateLtlResult
                        
    member internal this.atAnalyseLtl (ltlExpr:LtlExpr) : SafetySharp.Ternary.Ternary =
        let workflowToCalculateLtlResult =
            currentState.getLoadedModelCache.AtLtlFormulas.checkLtlFormula(ltlExpr)
        this.RunWorkflowOnModel_getResult workflowToCalculateLtlResult

    member this.atAnalyseLtl (formula:string) : SafetySharp.Ternary.Ternary = 
        let formulaAsLtlExpr = currentState.getLoadedModelCache.LtlExprParser formula
        this.atAnalyseLtl formulaAsLtlExpr 

        
        
    member internal this.atAnalyseDccaLtl_WithNuSmv (hazard:PropositionalExpr) : Set<Set<ScmHelpers.FaultPath>> = 
        let workflowToCalculateDccaResult =
            currentState.getLoadedModelCache.AtDccaLtl(hazard).checkWithNusmv()
        this.RunWorkflowOnModel_getResult workflowToCalculateDccaResult

    member internal this.atAnalyseDccaLtl_WithPromela (hazard:PropositionalExpr) : Set<Set<ScmHelpers.FaultPath>> = 
        let workflowToCalculateDccaResult =
            currentState.getLoadedModelCache.AtDccaLtl(hazard).checkWithPromela()
        this.RunWorkflowOnModel_getResult workflowToCalculateDccaResult

    member internal this.atAnalyseDccaLtl (hazard:PropositionalExpr) : Set<Set<ScmHelpers.FaultPath>> =  
        let workflowToCalculateDccaResult =
            currentState.getLoadedModelCache.AtDccaLtl(hazard).check()
        this.RunWorkflowOnModel_getResult workflowToCalculateDccaResult
    
    member this.atAnalyseDccaLtl (hazard:string) : Set<Set<string>> =  
        let hazardAsPropExpr = currentState.getLoadedModelCache.PropositionalExprParser hazard
        let result = this.atAnalyseDccaLtl hazardAsPropExpr
        result |> Set.map (fun s -> s |> Set.map (fun elem -> ScmToString.faultPathToString elem))

    
                
    member internal this.atAnalyseDccaPruning_WithPromela (hazard:PropositionalExpr) : Set<Set<ScmHelpers.FaultPath>> = 
        let workflowToCalculateDccaResult =
            currentState.getLoadedModelCache.AtDccaPruning(hazard).checkWithPromela()
        this.RunWorkflowOnModel_getResult workflowToCalculateDccaResult

    member internal this.atAnalyseDccaPruning_WithNuSmv (hazard:PropositionalExpr) : Set<Set<ScmHelpers.FaultPath>> = 
        let workflowToCalculateDccaResult =
            currentState.getLoadedModelCache.AtDccaPruning(hazard).checkWithNusmv()
        this.RunWorkflowOnModel_getResult workflowToCalculateDccaResult

    member internal this.atAnalyseDccaPruning (hazard:PropositionalExpr) : Set<Set<ScmHelpers.FaultPath>> = 
        let workflowToCalculateDccaResult =
            currentState.getLoadedModelCache.AtDccaPruning(hazard).check()
        this.RunWorkflowOnModel_getResult workflowToCalculateDccaResult
        
    member this.atAnalyseDccaPruning (hazard:string) : Set<Set<string>> =  
        let hazardAsPropExpr = currentState.getLoadedModelCache.PropositionalExprParser hazard
        let result = this.atAnalyseDccaPruning hazardAsPropExpr
        result |> Set.map (fun s -> s |> Set.map (fun elem -> ScmToString.faultPathToString elem))

    // Methods to organize state
    
    member this.removeTemporaryFiles () :unit =
        //TODO. Or maybe implement IDisposable
        ()

    member this.saveLogAsHtmlReport () :unit =
        //TODO. Or maybe implement IDisposable
        ()