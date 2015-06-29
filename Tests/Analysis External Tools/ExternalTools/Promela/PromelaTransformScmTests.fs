// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineeringgineering
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

type ScmToPromelaTests (xunitOutput:ITestOutputHelper) =


    static member testdataAll = TestCases.ScmSmokeTests.smoketestsAll
    static member testdataDeterministic = TestCases.ScmSmokeTests.smoketestsDeterministic        
        
    [<Theory>]
    [<MemberData("testdataDeterministic")>]
    member this.``check smoke tests with NuXmvGwamCheckSamSmokeTests`` (testname:string) =    

        let inputFileNameToOutputFileName (inputFile:string) : SafetySharp.FileSystem.FileName =
            let filenameWithoutPath = System.IO.Path.GetFileNameWithoutExtension inputFile
            let newDirectory = "../../Examples/Promela/TransformedScm.Generated"
            SafetySharp.FileSystem.FileName (sprintf "%s/%s.smv" newDirectory filenameWithoutPath)

        let inputFile = """../../Examples/SCM/""" + testname
        
        let smokeTestWorkflow = workflow {
                do! TestHelpers.addLogEventHandlerForXUnit (xunitOutput)
                do! setEngineOption(TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangesAfterStep)
                do! readFile inputFile
                do! SafetySharp.Models.ScmParser.parseStringWorkflow ()
                do! SafetySharp.Analysis.Modelchecking.PromelaSpin.ScmToPromela.transformConfiguration ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.PromelaSpin.PromelaToString.workflow ()
                do! printToLog ()
                let outputFile = inputFileNameToOutputFileName inputFile
                do! saveToFile outputFile
            }

        let output = SafetySharp.Workflow.runWorkflow_getState smokeTestWorkflow
        ()