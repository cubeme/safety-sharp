﻿// The MIT License (MIT)
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

namespace SafetySharp.ExternalTools.Smv

open Xunit
open Xunit.Abstractions

open SafetySharp.Models
open SafetySharp.Workflow
open SafetySharp.ExternalTools.Smv
open SafetySharp.EngineOptions

type SamToNuXmvTests (xunitOutput:ITestOutputHelper) =

    static member testdataAll = TestCases.SamSmokeTests.smoketestsAll
    static member testdataDeterministic = TestCases.SamSmokeTests.smoketestsDeterministic        
        
    [<Theory>]
    [<MemberData("testdataDeterministic")>]
    member this.``smoke tests gets converted to NuXmv (gwam method)`` (testname:string) =    

        let inputFileNameToOutputFileName (inputFile:string) : SafetySharp.FileSystem.FileName =
            let filenameWithoutPath = System.IO.Path.GetFileNameWithoutExtension inputFile
            let newDirectory = "../../Examples/Smv/TransformedSamGwam.Generated"
            SafetySharp.FileSystem.FileName (sprintf "%s/%s.smv" newDirectory filenameWithoutPath)

        let inputFile = """../../Examples/SAM/""" + testname
        
        let smokeTestWorkflow = workflow {
                do! TestHelpers.addLogEventHandlerForXUnit (xunitOutput)
                do! readFile inputFile
                do! setEngineOption(TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangesAfterStep)
                do! SafetySharp.Models.SamParser.parseStringWorkflow
                do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
                do! SafetySharp.Models.TsamExplicitlyApplySemanticsOfAssignmentToRangedVariables.applySemanticsWorkflow ()
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.transformTsamToGwaModelWorkflow ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformGwamToTsareWorkflow ()
                do! SafetySharp.ExternalTools.VcTransitionRelationToNuXmv.transformTsareToNuXmvWorkflow ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.ExternalTools.SmvToString.workflow ()
                let outputFile = inputFileNameToOutputFileName inputFile
                do! printToFile outputFile
            }
        let runSmokeTest (inputFile) =
            SafetySharp.Workflow.runWorkflow_getState smokeTestWorkflow
        let output = runSmokeTest inputFile
        do xunitOutput.WriteLine (sprintf "%s" output)
        ()

        
    [<Theory>]
    [<MemberData("testdataDeterministic")>]
    member this.``smoke tests gets converted to NuXmv (sp method)`` (testname:string) =    

        let inputFileNameToOutputFileName (inputFile:string) : SafetySharp.FileSystem.FileName =
            let filenameWithoutPath = System.IO.Path.GetFileNameWithoutExtension inputFile
            let newDirectory = "../../Examples/Smv/TransformedSamSp.Generated"
            SafetySharp.FileSystem.FileName (sprintf "%s/%s.smv" newDirectory filenameWithoutPath)

        let inputFile = """../../Examples/SAM/""" + testname
        
        let smokeTestWorkflow = workflow {
                do! TestHelpers.addLogEventHandlerForXUnit (xunitOutput)
                do! readFile inputFile
                do! setEngineOption(TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangesAfterStep)
                do! SafetySharp.Models.SamParser.parseStringWorkflow
                do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
                do! SafetySharp.Models.TsamExplicitlyApplySemanticsOfAssignmentToRangedVariables.applySemanticsWorkflow ()
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToPassiveForm_Original ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformTsamToTsareWithSpWorkflow ()
                do! SafetySharp.ExternalTools.VcTransitionRelationToNuXmv.transformTsareToNuXmvWorkflow ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.ExternalTools.SmvToString.workflow ()
                let outputFile = inputFileNameToOutputFileName inputFile
                do! printToFile outputFile
            }
        let runSmokeTest (inputFile) =
            SafetySharp.Workflow.runWorkflow_getState smokeTestWorkflow
        let output = runSmokeTest inputFile
        do xunitOutput.WriteLine (sprintf "%s" output)
        ()
