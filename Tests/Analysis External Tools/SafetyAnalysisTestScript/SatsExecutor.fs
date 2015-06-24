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

namespace SafetySharp.SafetyAnalysisTestScript


module internal SatsGenericExecutor =
    open Sats

module internal SatsSamExecutor =
    open Sats

module internal SatsScmExecutor =
    
    open Sats
    open SafetySharp.Workflow

    type VerificationResult = unit
    
    type SatsExecutionState = {
        ParsedModel : SafetySharp.Models.ScmMutable.SimpleScmMutable<SafetySharp.Models.Scm.Traceable> option;
        VerificationResults : Map<LetIdentifier,VerificationResult>;
    }

    type SatsExecutionResult =
        | FinishedSuccessful
        | InvalidInput
        | FailureDuringVerification
        
    let executeDoStatementWf (doStatement:DoStatement) : WorkflowFunction<SatsExecutionState,SatsExecutionState,SatsExecutionResult> = workflow {
        match doStatement with
            | DoStatement.SetEngineOption (iengineOption) ->
                do! setIEngineOption iengineOption
                return SatsExecutionResult.FinishedSuccessful
            | DoStatement.SetModel(filename) ->
                let! executionState = getState ()
                do! readFile filename
                do! SafetySharp.Models.ScmParser.parseStringWorkflow ()
                let! parsedModel = getState ()
                let newExecutionState =
                    { executionState with
                        SatsExecutionState.ParsedModel = Some(parsedModel);
                    }
                do! updateState newExecutionState
                return SatsExecutionResult.FinishedSuccessful
    }

    let executeLetStatementtWf (letStatement:LetStatement) : WorkflowFunction<SatsExecutionState,SatsExecutionState,SatsExecutionResult> = workflow {
        match letStatement with
            | LetStatement.AtLtlFormula (letIdentifier,formula) ->
                let! executionState = getState ()
                let model = executionState.ParsedModel.Value.Model
                //let ltlAnalyzer = SafetySharp.AnalysisTechniques.AtLtlFormula.AnalyseLtlFormulas(model)
                //do ltlAnalyzer.addLtlFormula ()
                //do ltlAnalyzer.checkWithPromela()
                let newExecutionState =
                    { executionState with
                        SatsExecutionState.VerificationResults = executionState.VerificationResults;
                    }
                return SatsExecutionResult.FinishedSuccessful                
            | LetStatement.AtDccaLtl (letIdentifier,hazard) ->
                let! executionState = getState ()
                let model = executionState.ParsedModel.Value.Model
                //let hazard = SafetySharp.Models.ScmParser.
                //let dccaLtlAnalyzer = SafetySharp.AnalysisTechniques.AtDccaLtl.PerformDccaWithLtlFormulas (model,hazard)
                //let result = dccaLtlAnalyzer.checkWithNuSMV()
                let newExecutionState =
                    { executionState with
                        SatsExecutionState.VerificationResults = executionState.VerificationResults;
                    }
                return SatsExecutionResult.FinishedSuccessful     
    }

    let executeExpectStatementWf (expectStatement:ExpectStatement) : WorkflowFunction<SatsExecutionState,SatsExecutionState,SatsExecutionResult> = workflow {
        return SatsExecutionResult.FinishedSuccessful
    }

    let executeSatsStatementWf (previousResult:SatsExecutionResult) (satsStatement:SatsStatement)
                : WorkflowFunction<SatsExecutionState,SatsExecutionState,SatsExecutionResult> = workflow {
        match previousResult with
            | FinishedSuccessful ->
                match satsStatement with
                    | SatsStatement.DoStatement (doStatement) -> return! (executeDoStatementWf doStatement)
                    | SatsStatement.LetStatement (letStatement) -> return! (executeLetStatementtWf letStatement)
                    | SatsStatement.ExpectStatement (expectStatement) -> return! (executeExpectStatementWf expectStatement)
            | _ ->
                return previousResult
    }

    let executeSatsPgmWf : WorkflowFunction<SatsPgm,SatsExecutionResult,unit> = workflow {
        let! satsPgm = getState ()
        let initialExecutionState =
            {
                SatsExecutionState.ParsedModel = None;
                SatsExecutionState.VerificationResults = Map.empty<LetIdentifier,VerificationResult>;
            }
        do! updateState initialExecutionState
        let! finalExecutionResult = listFold executeSatsStatementWf (SatsExecutionResult.FinishedSuccessful) (satsPgm.Pgm)
        do! updateState SatsExecutionResult.FinishedSuccessful
    }

    let executeSatsPgmFileWf (filename:string) (engineOptions:SafetySharp.EngineOptions.IEngineOption list)
            : WorkflowFunction<unit,SatsExecutionResult,unit> = workflow {
        do! listIter_seqState setIEngineOption engineOptions
        do! readFile filename
        do! SatsParser.parseStringWorkflow ()
        do! executeSatsPgmWf
    }
    
    let executeSatsPgmFile = executeSatsPgmFileWf
