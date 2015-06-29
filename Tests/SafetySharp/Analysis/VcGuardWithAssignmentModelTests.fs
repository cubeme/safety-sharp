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

namespace Models.Tsam

open Xunit
open Xunit.Abstractions

open SafetySharp.Models.Sam
open SafetySharp.Models.Tsam
open SafetySharp.Workflow
open SafetySharp.Models
open SafetySharp.EngineOptions

type VcGuardWithAssignmentModelTests(xunitOutput:ITestOutputHelper) =
    

    static member testdataAll = TestCases.SamSmokeTests.smoketestsAll
    static member testdataDeterministic = TestCases.SamSmokeTests.smoketestsDeterministic  
    
    
    [<Theory>]
    [<MemberData("testdataAll")>]
    member this.``convert smokeTest to Gwa Form (ranges after step)`` (testname:string) =    
        let inputFile = """../../Examples/SAM/""" + testname
        
        let smokeTestWithGwamWorkflow = workflow {
                do! TestHelpers.addLogEventHandlerForXUnit (xunitOutput)
                do! setEngineOption(TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangesAfterStep)
                do! readFile inputFile
                do! SafetySharp.Models.SamParser.parseStringWorkflow
                do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
                do! SafetySharp.Models.TsamExplicitlyApplySemanticsOfAssignmentToRangedVariables.applySemanticsWorkflow ()
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.transformTsamToTsamInGuardToAssignmentForm()

                //do! SafetySharp.Workflow.printObjectToLog ()
                //do! SafetySharp.Workflow.printNewParagraphToLog ()
                do! SafetySharp.Models.TsamToString.exportModelWorkflow ()
                //do! SafetySharp.Workflow.printToLog ()
            }
        let runSmokeTest (inputFile) =
            SafetySharp.Workflow.runWorkflow_getState smokeTestWithGwamWorkflow
        let output = runSmokeTest inputFile
        do xunitOutput.WriteLine (sprintf "%s" output)
        ()
        
    
    [<Theory>]
    [<MemberData("testdataAll")>]
    member this.``convert smokeTest to Gwa Form (ranges after every assignment)`` (testname:string) =    
        let inputFile = """../../Examples/SAM/""" + testname
        
        let smokeTestWithGwamWorkflow = workflow {
                do! TestHelpers.addLogEventHandlerForXUnit (xunitOutput)
                do! setEngineOption(TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangeAfterEveryAssignmentToAGlobalVar)
                do! readFile inputFile
                do! SafetySharp.Models.SamParser.parseStringWorkflow
                do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
                do! SafetySharp.Models.TsamExplicitlyApplySemanticsOfAssignmentToRangedVariables.applySemanticsWorkflow ()
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.transformTsamToTsamInGuardToAssignmentForm()

                //do! SafetySharp.Workflow.printObjectToLog ()
                //do! SafetySharp.Workflow.printNewParagraphToLog ()
                do! SafetySharp.Models.TsamToString.exportModelWorkflow ()
                //do! SafetySharp.Workflow.printToLog ()
            }
        let runSmokeTest (inputFile) =
            SafetySharp.Workflow.runWorkflow_getState smokeTestWithGwamWorkflow
        let output = runSmokeTest inputFile
        do xunitOutput.WriteLine (sprintf "%s" output)
        ()
        
    
    [<Theory>]
    [<MemberData("testdataAll")>]
    member this.``convert smokeTest to Gwa Model (ranges after step)`` (testname:string) =    

        let inputFile = """../../Examples/SAM/""" + testname
        
        let smokeTestWithGwamWorkflow = workflow {
                do! TestHelpers.addLogEventHandlerForXUnit (xunitOutput)
                do! setEngineOption(TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangesAfterStep)
                do! readFile inputFile
                do! SafetySharp.Models.SamParser.parseStringWorkflow
                do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
                do! SafetySharp.Models.TsamExplicitlyApplySemanticsOfAssignmentToRangedVariables.applySemanticsWorkflow ()
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.transformTsamToGwaModelWorkflow()
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.modelToStringWorkflow ()

                //do! SafetySharp.Workflow.printObjectToLog ()
                //do! SafetySharp.Workflow.printNewParagraphToLog ()
                //do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.guardWithAssignmentModelToString ()
            }
        let runSmokeTest (inputFile) =
            SafetySharp.Workflow.runWorkflow_getState smokeTestWithGwamWorkflow
        let output = runSmokeTest inputFile
        do xunitOutput.WriteLine (sprintf "%s" output)
        ()
    
    [<Theory>]
    [<MemberData("testdataAll")>]
    member this.``convert smokeTest to Gwa Model (ranges after every assignment)`` (testname:string) =    

        let inputFile = """../../Examples/SAM/""" + testname
        
        let smokeTestWithGwamWorkflow = workflow {
                do! TestHelpers.addLogEventHandlerForXUnit (xunitOutput)
                do! setEngineOption(TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangeAfterEveryAssignmentToAGlobalVar)
                do! readFile inputFile
                do! SafetySharp.Models.SamParser.parseStringWorkflow
                do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
                do! SafetySharp.Models.TsamExplicitlyApplySemanticsOfAssignmentToRangedVariables.applySemanticsWorkflow ()
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.transformTsamToGwaModelWorkflow()
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.modelToStringWorkflow ()

                //do! SafetySharp.Workflow.printObjectToLog ()
                //do! SafetySharp.Workflow.printNewParagraphToLog ()
                //do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.guardWithAssignmentModelToString ()
            }
        let runSmokeTest (inputFile) =
            SafetySharp.Workflow.runWorkflow_getState smokeTestWithGwamWorkflow
        let output = runSmokeTest inputFile
        do xunitOutput.WriteLine (sprintf "%s" output)
        ()
        