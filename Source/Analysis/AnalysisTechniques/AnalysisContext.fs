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

type private LoadedModelCache = {    
    PropositionalExprParser : string -> ScmVerificationElements.PropositionalExpr;
    LtlExprParser : string -> ScmVerificationElements.LtlExpr;
}
    with
        static member initial (scmModel: Scm.ScmModel ) =
            let initialParserState = SafetySharp.Models.ScmVeParser.UserState.initialUserState scmModel
            {
                LoadedModelCache.PropositionalExprParser = SafetySharp.Models.ScmVeParser.propositionalExprParser_Result initialParserState
                LoadedModelCache.LtlExprParser = SafetySharp.Models.ScmVeParser.ltlExprParser_Result initialParserState
            }

[<RequireQualifiedAccessAttribute>]
type private AnalysisContextState =
    | Uninitialized of WorkflowState:WorkflowState<unit>
    | ModelLoaded of LoadedModel:ScmTracer.SimpleScmTracer<Scm.Traceable> *
                     LoadedModelCache:LoadedModelCache *
                     WorkflowState:WorkflowState<ScmTracer.SimpleScmTracer<Scm.Traceable>>
    with
        member this.getLoadedModel : ScmTracer.SimpleScmTracer<Scm.Traceable> =
            match this with
                | AnalysisContextState.Uninitialized (_) ->
                    failwith "Unable to perform action on model because currently no model has been loaded."
                | AnalysisContextState.ModelLoaded (currentModel,currentModelCache,wfState) ->
                    currentModel
        member this.getLoadedModelCache : LoadedModelCache =
            match this with
                | AnalysisContextState.Uninitialized (_) ->
                    failwith "Unable to perform action on model because currently no model has been loaded."
                | AnalysisContextState.ModelLoaded (currentModel,currentModelCache,wfState) ->
                    currentModelCache

// Note: Not thread safe
type AnalysisContext () =
    
    let mutable currentState : AnalysisContextState = AnalysisContextState.Uninitialized(workflowState_emptyInit ())

    //////// Workflow /////////////

    // Every call may change every content (log/engineoption) of wfState except the inner state. The inner state is always the baseModel
    member private this.RunWorkflowOnModel_getResult<'returnType,'resultingState>
                        (WorkflowFunction s:(WorkflowFunction<ScmTracer.SimpleScmTracer<Scm.Traceable>,'resultingState,'returnType>))
                        : 'returnType =
        match currentState with
            | AnalysisContextState.Uninitialized (_) ->
                failwith "Unable to perform action on model because currently no model has been loaded."
            | AnalysisContextState.ModelLoaded (currentModel,currentModelCache,wfState) ->
                let result,resultingWfState = s wfState
                let resultingWfStateWithCurrentModel =
                    {
                        WorkflowState.State = currentModel;
                        WorkflowState.StepNumber = resultingWfState.StepNumber;
                        WorkflowState.StepName = resultingWfState.StepName;
                        WorkflowState.Log = resultingWfState.Log;
                        WorkflowState.LogEvent = resultingWfState.LogEvent;
                        WorkflowState.EngineOptions = resultingWfState.EngineOptions;
                        WorkflowState.CancellationToken = resultingWfState.CancellationToken;
                        WorkflowState.Tainted = false;
                    }
                currentState <- AnalysisContextState.ModelLoaded(currentModel,currentModelCache,resultingWfStateWithCurrentModel)
                result
                
    // Every call may change every content (log/engineoption) of wfState except the inner state. The inner state is always the baseModel
    member private this.RunWorkflowOnModel_getState<'returnType,'resultingState>
                        (WorkflowFunction s:(WorkflowFunction<ScmTracer.SimpleScmTracer<Scm.Traceable>,'resultingState,'returnType>))
                        : 'resultingState =
        match currentState with
            | AnalysisContextState.Uninitialized (_) ->
                failwith "Unable to perform action on model because currently no model has been loaded."
            | AnalysisContextState.ModelLoaded (currentModel,currentModelCache,wfState) ->
                let result,resultingWfState = s wfState
                let resultingWfStateWithCurrentModel =
                    {
                        WorkflowState.State = currentModel;
                        WorkflowState.StepNumber = resultingWfState.StepNumber;
                        WorkflowState.StepName = resultingWfState.StepName;
                        WorkflowState.Log = resultingWfState.Log;
                        WorkflowState.LogEvent = resultingWfState.LogEvent;
                        WorkflowState.EngineOptions = resultingWfState.EngineOptions;
                        WorkflowState.CancellationToken = resultingWfState.CancellationToken;
                        WorkflowState.Tainted = false;
                    }
                currentState <- AnalysisContextState.ModelLoaded(currentModel,currentModelCache,resultingWfStateWithCurrentModel)
                resultingWfState.State
                                
    //////// Loading Main Model /////////////

    member internal this.setMainModel (_baseModel:ScmTracer.SimpleScmTracer<Scm.Traceable>) : unit =
        match currentState with
            | AnalysisContextState.ModelLoaded (_,_,wfState) ->
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
                currentState <- AnalysisContextState.ModelLoaded(_baseModel,LoadedModelCache.initial _baseModel.Model,newWfState)
                ()
            | AnalysisContextState.Uninitialized (wfState) ->
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
                currentState <- AnalysisContextState.ModelLoaded(_baseModel,LoadedModelCache.initial _baseModel.Model,newWfState)
                ()
                
    member internal this.setMainModelFromFile (filename:string) : unit =
        let readFromFileWorkflow (filename:string) = workflow {
            do! readFile filename
            do! SafetySharp.Models.ScmParser.parseStringWorkflow ()
        }
        match currentState with
            | AnalysisContextState.Uninitialized (wfState) ->
                let s = match readFromFileWorkflow filename with | WorkflowFunction(s) -> s
                let _,newWfStateAfterLoading = s wfState
                currentState <- AnalysisContextState.ModelLoaded(newWfStateAfterLoading.State,LoadedModelCache.initial newWfStateAfterLoading.State.Model,newWfStateAfterLoading)
                ()
            | AnalysisContextState.ModelLoaded (_,_,wfState) ->
                let s = match readFromFileWorkflow filename with | WorkflowFunction(s) -> s
                let _,newWfStateAfterLoading = s wfState
                currentState <- AnalysisContextState.ModelLoaded(newWfStateAfterLoading.State,LoadedModelCache.initial newWfStateAfterLoading.State.Model,newWfStateAfterLoading)
                ()

                
    //////// Engine Option /////////////

    member this.setEngineOption (engineOption:SafetySharp.EngineOptions.IEngineOption) : unit =
        // may be set whether a model is loaded or not
        match currentState with
            | AnalysisContextState.Uninitialized (wfState) ->
                let s = match SafetySharp.Workflow.setIEngineOption engineOption with | WorkflowFunction(s) -> s
                let _,newWfState = s wfState
                currentState <- AnalysisContextState.Uninitialized(newWfState)
                ()
            | AnalysisContextState.ModelLoaded (currentModel,currentModelCache,wfState) ->
                let s = match SafetySharp.Workflow.setIEngineOption engineOption with | WorkflowFunction(s) -> s
                let _,newWfState = s wfState
                currentState <- AnalysisContextState.ModelLoaded(currentModel,currentModelCache,newWfState)
                ()

    // Analysis Techniques
    
    member internal this.atAnalyseLtl (ltlExpr:LtlExpr) : SafetySharp.Ternary.Ternary = 
        SafetySharp.Ternary.Unknown

    member this.atAnalyseLtl (formula:string) : SafetySharp.Ternary.Ternary = 
        let formulaAsLtlExpr = currentState.getLoadedModelCache.LtlExprParser formula
        this.atAnalyseLtl formulaAsLtlExpr                
    
    member internal this.atAnalyseDccaLtl (hazard:PropositionalExpr) : Set<ScmHelpers.FaultPath> list = 
        []

    member this.atAnalyseDccaLtl (hazard:string) : Set<ScmHelpers.FaultPath> list =  
        let hazardAsPropExpr = currentState.getLoadedModelCache.PropositionalExprParser hazard
        this.atAnalyseDccaLtl hazardAsPropExpr