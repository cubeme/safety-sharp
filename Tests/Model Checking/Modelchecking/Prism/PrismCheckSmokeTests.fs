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

namespace SafetySharp.Modelchecking
    
open Xunit
open Xunit.Abstractions

open SafetySharp.Models
open SafetySharp.Workflow

type PrismCheckSmokeTests (xunitOutput:ITestOutputHelper) =
    

    static member internal addLogEventHandlerForXUnit<'state> (output:Xunit.Abstractions.ITestOutputHelper) : SafetySharp.Workflow.EndogenousWorkflowFunction<'state> = 
        let behavior (wfState:SafetySharp.Workflow.WorkflowState<'state>) =
            do wfState.LogEvent.Publish.Add (
                fun text -> output.WriteLine text
            )
            (),wfState
        SafetySharp.Workflow.WorkflowFunction(behavior)

    static member testdataAll = TestCases.SamSmokeTests.smoketestsAll
    static member testdataDeterministic = TestCases.SamSmokeTests.smoketestsDeterministic        
        
    [<Theory>]
    [<MemberData("testdataDeterministic")>]
    member this.``check smoke tests with gwam fast method`` (testname:string) =    
        let inputFileNameToOutputFileName (inputFile:string) : SafetySharp.FileSystem.FileName =
            let filenameWithoutPath = System.IO.Path.GetFileNameWithoutExtension inputFile
            let newDirectory = "../../Examples/Prism/TransformedSamWithGwamFast"
            SafetySharp.FileSystem.FileName (sprintf "%s/%s.prism" newDirectory filenameWithoutPath)

        let inputFile = """../../Examples/SAM/""" + testname
        
        let smokeTestWithGwamWorkflow = workflow {
                do! PrismCheckSmokeTests.addLogEventHandlerForXUnit (xunitOutput)
                do! readFile inputFile
                do! SafetySharp.Models.SamParser.parseStringWorkflow
                do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModelFast.transformWorkflow ()
                do! SafetySharp.Analysis.Modelchecking.Prism.GwamToPrism.transformWorkflow ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.Prism.ExportPrismAstToFile.workflow ()
                let outputFile = inputFileNameToOutputFileName inputFile
                do! printToFile outputFile
            }
        let runSmokeTest (inputFile) =
            SafetySharp.Workflow.runWorkflow_getState smokeTestWithGwamWorkflow
        let output = runSmokeTest inputFile
        do xunitOutput.WriteLine (sprintf "%s" output)
        ()

        
    [<Theory>]
    [<MemberData("testdataAll")>]
    member this.``check smoke tests with gwam method`` (testname:string) =    
        let inputFileNameToOutputFileName (inputFile:string) : SafetySharp.FileSystem.FileName =
            let filenameWithoutPath = System.IO.Path.GetFileNameWithoutExtension inputFile
            let newDirectory = "../../Examples/Prism/TransformedSamWithGwam"
            SafetySharp.FileSystem.FileName (sprintf "%s/%s.prism" newDirectory filenameWithoutPath)

        let inputFile = """../../Examples/SAM/""" + testname
        
        let smokeTestWithGwamWorkflow = workflow {
                do! PrismCheckSmokeTests.addLogEventHandlerForXUnit (xunitOutput)
                do! readFile inputFile
                do! SafetySharp.Models.SamParser.parseStringWorkflow
                do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.transformTsamToGwaModelWorkflow ()
                do! SafetySharp.Analysis.Modelchecking.Prism.GwamToPrism.transformWorkflow ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.Prism.ExportPrismAstToFile.workflow ()
                let outputFile = inputFileNameToOutputFileName inputFile
                do! printToFile outputFile
            }
        let runSmokeTest (inputFile) =
            SafetySharp.Workflow.runWorkflow_getState smokeTestWithGwamWorkflow
        let output = runSmokeTest inputFile
        do xunitOutput.WriteLine (sprintf "%s" output)
        ()


    [<Theory>]
    [<MemberData("testdataAll")>]
    member this.``check smoke tests with plain method`` (testname:string) =    
        let inputFileNameToOutputFileName (inputFile:string) : SafetySharp.FileSystem.FileName =
            let filenameWithoutPath = System.IO.Path.GetFileNameWithoutExtension inputFile
            let newDirectory = "../../Examples/Prism/TransformedSamWithPlain"
            SafetySharp.FileSystem.FileName (sprintf "%s/%s.prism" newDirectory filenameWithoutPath)

        let inputFile = """../../Examples/SAM/""" + testname
        
        let smokeTestWithGwamWorkflow = workflow {
                do! PrismCheckSmokeTests.addLogEventHandlerForXUnit (xunitOutput)
                do! readFile inputFile
                do! SafetySharp.Models.SamParser.parseStringWorkflow
                do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
                do! SafetySharp.Models.TsamToSpg.transformToStochasticProgramGraphWorkflow ()
                do! SafetySharp.Analysis.Modelchecking.Prism.StochasticProgramGraphToPrism.transformWorkflow ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.Prism.ExportPrismAstToFile.workflow ()
                let outputFile = inputFileNameToOutputFileName inputFile
                do! printToFile outputFile
            }
        let runSmokeTest (inputFile) =
            SafetySharp.Workflow.runWorkflow_getState smokeTestWithGwamWorkflow
        let output = runSmokeTest inputFile
        do xunitOutput.WriteLine (sprintf "%s" output)
        ()