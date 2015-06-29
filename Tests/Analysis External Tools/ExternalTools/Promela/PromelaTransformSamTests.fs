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

namespace SafetySharp.ExternalTools.PromelaSpin
    
open Xunit
open Xunit.Abstractions

open SafetySharp.Models
open SafetySharp.Workflow
open SafetySharp.EngineOptions

type SamToPromelaTests (xunitOutput:ITestOutputHelper) =
    

    static member testdataAll = TestCases.SamSmokeTests.smoketestsAll
    static member testdataDeterministic = TestCases.SamSmokeTests.smoketestsDeterministic        
        
    [<Theory>]
    [<MemberData("testdataDeterministic")>]
    member this.``check smoke tests with EngineOption IgnoreRanges`` (testname:string) =    
        let inputFileNameToOutputFileName (inputFile:string) : SafetySharp.FileSystem.FileName =
            let filenameWithoutPath = System.IO.Path.GetFileNameWithoutExtension inputFile
            let newDirectory = "../../Examples/Promela/TransformedSam_IgnoreRanges.Generated"
            SafetySharp.FileSystem.FileName (sprintf "%s/%s.pml" newDirectory filenameWithoutPath)

        let inputFile = """../../Examples/SAM/""" + testname
        
        let smokeTestWithGwamWorkflow = workflow {
                do! TestHelpers.addLogEventHandlerForXUnit (xunitOutput)
                do! setEngineOption(TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.IgnoreRanges)
                do! readFile inputFile
                do! SafetySharp.Models.SamParser.parseStringWorkflow
                do! SafetySharp.Analysis.Modelchecking.PromelaSpin.SamToPromela.transformConfigurationWf ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.PromelaSpin.PromelaToString.workflow ()
                let outputFile = inputFileNameToOutputFileName inputFile
                do! printToLog ()
                do! saveToFile outputFile
            }
        let runSmokeTest (inputFile) =
            SafetySharp.Workflow.runWorkflow_getState smokeTestWithGwamWorkflow
        let output = runSmokeTest inputFile
        ()
        
    [<Theory>]
    [<MemberData("testdataDeterministic")>]
    member this.``check smoke tests with EngineOption ForceRangesAfterStep`` (testname:string) =    
        let inputFileNameToOutputFileName (inputFile:string) : SafetySharp.FileSystem.FileName =
            let filenameWithoutPath = System.IO.Path.GetFileNameWithoutExtension inputFile
            let newDirectory = "../../Examples/Promela/TransformedSam_ForceRangesAfterStep.Generated"
            SafetySharp.FileSystem.FileName (sprintf "%s/%s.pml" newDirectory filenameWithoutPath)

        let inputFile = """../../Examples/SAM/""" + testname
        
        let smokeTestWithGwamWorkflow = workflow {
                do! TestHelpers.addLogEventHandlerForXUnit (xunitOutput)
                do! setEngineOption(TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangesAfterStep)
                do! readFile inputFile
                do! SafetySharp.Models.SamParser.parseStringWorkflow
                do! SafetySharp.Analysis.Modelchecking.PromelaSpin.SamToPromela.transformConfigurationWf ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.PromelaSpin.PromelaToString.workflow ()
                do! printToLog ()
                let outputFile = inputFileNameToOutputFileName inputFile
                do! saveToFile outputFile
            }
        let runSmokeTest (inputFile) =
            SafetySharp.Workflow.runWorkflow_getState smokeTestWithGwamWorkflow
        let output = runSmokeTest inputFile
        ()

    [<Theory>]
    [<MemberData("testdataDeterministic")>]
    member this.``check smoke tests with EngineOption ForceRangeAfterEveryAssignmentToAGlobalVar`` (testname:string) =    
        let inputFileNameToOutputFileName (inputFile:string) : SafetySharp.FileSystem.FileName =
            let filenameWithoutPath = System.IO.Path.GetFileNameWithoutExtension inputFile
            let newDirectory = "../../Examples/Promela/TransformedSam_ForceRangeAfterEveryAssignmentToAGlobalVar.Generated"
            SafetySharp.FileSystem.FileName (sprintf "%s/%s.pml" newDirectory filenameWithoutPath)

        let inputFile = """../../Examples/SAM/""" + testname
        
        let smokeTestWithGwamWorkflow = workflow {
                do! TestHelpers.addLogEventHandlerForXUnit (xunitOutput)
                do! setEngineOption(TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangeAfterEveryAssignmentToAGlobalVar)
                do! readFile inputFile
                do! SafetySharp.Models.SamParser.parseStringWorkflow
                do! SafetySharp.Analysis.Modelchecking.PromelaSpin.SamToPromela.transformConfigurationWf ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.PromelaSpin.PromelaToString.workflow ()
                do! printToLog ()
                let outputFile = inputFileNameToOutputFileName inputFile
                do! saveToFile outputFile
            }
        let runSmokeTest (inputFile) =
            SafetySharp.Workflow.runWorkflow_getState smokeTestWithGwamWorkflow
        let output = runSmokeTest inputFile
        ()