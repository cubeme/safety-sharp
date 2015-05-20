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

open NUnit.Framework
open SafetySharp.Workflow
open SafetySharp.Models

[<TestFixture>]
module VcGuardWithAssignmentModelTests =
    open SafetySharp.Models.Sam
    open SafetySharp.Models.Tsam

    let internal readInputFileAndTransformToGwaForm (inputFile:string) = workflow {
            do! readFile inputFile
            do! SafetySharp.Models.SamParser.parseStringWorkflow
            do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
            do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
            do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.transformTsamToTsamInGuardToAssignmentForm()

            do! SafetySharp.Workflow.printObjectToStdout ()
            do! SafetySharp.Workflow.printNewParagraphToStdout ()
            do! SafetySharp.Models.TsamToString.exportModelWorkflow ()
            do! SafetySharp.Workflow.printToStdout ()
    }
    
    [<Test>]
    let ``smokeTest1 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest1.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest2 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest2.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    let ``smokeTest3 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest3.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()
        
    [<Test>]
    let ``smokeTest4 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest4.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest5 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest5.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest6 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest6.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest7 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest7.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest8 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest8.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest9 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest9.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest10 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest10.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest11 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest11.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest12 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest12.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest13 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest13.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest14 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest14.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest15 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest15.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest16 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest16.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest17 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest17.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest18 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest18.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest19 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest19.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest20 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest20.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest21 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest21.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``smokeTest22 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/smokeTest22.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``nestedBlocks1 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/nestedBlocks1.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()

    [<Test>]
    let ``nestedBlocks2 gets converted to Gwa Form`` () =
        let inputFile = """../../Examples/SAM/nestedBlocks2.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaForm inputFile)
        ()



        

    let internal readInputFileAndTransformToGwaModel (inputFile:string) = workflow {
            do! readFile inputFile
            do! SafetySharp.Models.SamParser.parseStringWorkflow
            do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
            do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
            do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.transformTsamToGwaModelWorkflow ()

            do! SafetySharp.Workflow.printObjectToStdout ()
            do! SafetySharp.Workflow.printNewParagraphToStdout ()
            //do! SafetySharp.Models.TsamToString.exportModelWorkflow ()
            //do! SafetySharp.Workflow.printToStdout ()
    }
    
    [<Test>]
    let ``smokeTest1 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest1.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest2 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest2.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    let ``smokeTest3 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest3.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()
        
    [<Test>]
    let ``smokeTest4 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest4.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest5 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest5.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest6 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest6.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest7 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest7.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest8 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest8.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest9 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest9.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest10 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest10.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest11 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest11.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest12 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest12.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest13 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest13.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest14 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest14.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest15 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest15.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest16 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest16.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest17 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest17.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest18 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest18.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest19 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest19.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest20 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest20.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest21 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest21.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``smokeTest22 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/smokeTest22.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``nestedBlocks1 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/nestedBlocks1.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()

    [<Test>]
    let ``nestedBlocks2 gets converted to Gwa Model`` () =
        let inputFile = """../../Examples/SAM/nestedBlocks2.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndTransformToGwaModel inputFile)
        ()