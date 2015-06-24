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

    type VerificationResult = unit
    
    type SatsExecutionState = {
        AnalysisContext : SafetySharp.AnalysisTechniques.AnalysisContext;
        VerificationResults : Map<LetIdentifier,VerificationResult>;
    }

    type SatsExecutionResult =
        | FinishedSuccessful
        | InvalidInput
        | FailureDuringVerification
        
    let executeDoStatement (previousState:SatsExecutionState) (doStatement:DoStatement) : SatsExecutionState*SatsExecutionResult =
        match doStatement with
            | DoStatement.SetEngineOption (engineOption) ->
                do previousState.AnalysisContext.setEngineOption (engineOption)
                (previousState,SatsExecutionResult.FinishedSuccessful)
            | DoStatement.SetMainModel(filename) ->
                do previousState.AnalysisContext.setMainModelFromFile (filename)
                (previousState,SatsExecutionResult.FinishedSuccessful)

    let executeLetStatement (previousState:SatsExecutionState) (letStatement:LetStatement) : SatsExecutionState*SatsExecutionResult =
        match letStatement with
            | LetStatement.AtLtlFormula (letIdentifier,formula) ->
                //let ltlAnalyzer = SafetySharp.AnalysisTechniques.AtLtlFormula.AnalyseLtlFormulas(model)
                //do ltlAnalyzer.addLtlFormula ()
                //do ltlAnalyzer.checkWithPromela()
                let newExecutionState =
                    { previousState with
                        SatsExecutionState.VerificationResults = previousState.VerificationResults;
                    }
                (newExecutionState, SatsExecutionResult.FinishedSuccessful)
            | LetStatement.AtDccaLtl (letIdentifier,hazard) ->
                //let hazard = SafetySharp.Models.ScmParser.
                //let dccaLtlAnalyzer = SafetySharp.AnalysisTechniques.AtDccaLtl.PerformDccaWithLtlFormulas (model,hazard)
                //let result = dccaLtlAnalyzer.checkWithNuSMV()
                let newExecutionState =
                    { previousState with
                        SatsExecutionState.VerificationResults = previousState.VerificationResults;
                    }
                (newExecutionState, SatsExecutionResult.FinishedSuccessful)

    let executeExpectStatement (previousState:SatsExecutionState) (expectStatement:ExpectStatement) : SatsExecutionState*SatsExecutionResult =
        (previousState,SatsExecutionResult.FinishedSuccessful)

    let executeSatsStatement (previousState:SatsExecutionState,previousResult:SatsExecutionResult) (satsStatement:SatsStatement) : SatsExecutionState*SatsExecutionResult =
        match previousResult with
            | FinishedSuccessful ->
                match satsStatement with
                    | SatsStatement.DoStatement (doStatement) -> executeDoStatement previousState doStatement
                    | SatsStatement.LetStatement (letStatement) -> executeLetStatement previousState letStatement
                    | SatsStatement.ExpectStatement (expectStatement) -> executeExpectStatement previousState expectStatement
            | _ ->
                (previousState,previousResult)

    let executeSatsPgm (satsPgm:SatsPgm) (engineOptions:SafetySharp.EngineOptions.IEngineOption list) : SatsExecutionState*SatsExecutionResult =
        let initialExecutionState =
            {
                SatsExecutionState.AnalysisContext = new SafetySharp.AnalysisTechniques.AnalysisContext();
                SatsExecutionState.VerificationResults = Map.empty<LetIdentifier,VerificationResult>;
            }
        do engineOptions |> List.iter (fun engineOption -> initialExecutionState.AnalysisContext.setEngineOption engineOption)
        let finalExecutionState,finalExecutionResult = (satsPgm.Pgm) |> List.fold executeSatsStatement (initialExecutionState,SatsExecutionResult.FinishedSuccessful) 
        finalExecutionState,finalExecutionResult

    
    let executeSatsPgmFile (filename:string) (engineOptions:SafetySharp.EngineOptions.IEngineOption list) : SatsExecutionState*SatsExecutionResult =
        let input = System.IO.File.ReadAllText filename
        let satsPgm = SatsParser.parseSatsFile input
        let finalExecutionState,finalExecutionResult = executeSatsPgm satsPgm engineOptions
        finalExecutionState,finalExecutionResult

    open SafetySharp.Workflow

    let executeSatsPgmFileWf (filename:string) (engineOptions:SafetySharp.EngineOptions.IEngineOption list)
            : WorkflowFunction<unit,SatsExecutionState*SatsExecutionResult,unit> = workflow {
        let result = executeSatsPgmFile filename engineOptions
        do! updateState result
    }
    
