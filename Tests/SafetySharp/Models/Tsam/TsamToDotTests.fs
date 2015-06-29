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
module TsamToDotTests =

    let internal inputFileNameToOutputFileName (inputFile:string) : SafetySharp.FileSystem.FileName =
        let filenameWithoutPath = System.IO.Path.GetFileNameWithoutExtension inputFile
        let newDirectory = "../../Examples/Dot/TsamAsDot.Generated"
        SafetySharp.FileSystem.FileName (sprintf "%s/%s.gv" newDirectory filenameWithoutPath)
                        
    let internal readInputFileAndGenerateDotFile (inputFile:string) = workflow {
            do! readFile inputFile
            do! SafetySharp.Models.SamParser.parseStringWorkflow
            do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
            do! SafetySharp.Models.TsamToDot.exportModelWorkflow ()
            do! SafetySharp.GraphVizDot.DotToString.exportDotPlainFile ()

            do! SafetySharp.Workflow.printToLog ()
            let outputFile = inputFileNameToOutputFileName inputFile
            do! printToFile outputFile
    }

    [<Test>]
    let ``create dot graph of smokeTest1`` () =
        let inputFile = """../../Examples/SAM/smokeTest1.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest2`` () =
        let inputFile = """../../Examples/SAM/smokeTest2.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    let ``create dot graph of smokeTest3`` () =
        let inputFile = """../../Examples/SAM/smokeTest3.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()
        
    [<Test>]
    let ``create dot graph of smokeTest4`` () =
        let inputFile = """../../Examples/SAM/smokeTest4.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest5`` () =
        let inputFile = """../../Examples/SAM/smokeTest5.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest6`` () =
        let inputFile = """../../Examples/SAM/smokeTest6.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest7`` () =
        let inputFile = """../../Examples/SAM/smokeTest7.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest8`` () =
        let inputFile = """../../Examples/SAM/smokeTest8.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest9`` () =
        let inputFile = """../../Examples/SAM/smokeTest9.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest10`` () =
        let inputFile = """../../Examples/SAM/smokeTest10.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest11`` () =
        let inputFile = """../../Examples/SAM/smokeTest11.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest12`` () =
        let inputFile = """../../Examples/SAM/smokeTest12.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest13`` () =
        let inputFile = """../../Examples/SAM/smokeTest13.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest14`` () =
        let inputFile = """../../Examples/SAM/smokeTest14.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest15`` () =
        let inputFile = """../../Examples/SAM/smokeTest15.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest16`` () =
        let inputFile = """../../Examples/SAM/smokeTest16.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest17`` () =
        let inputFile = """../../Examples/SAM/smokeTest17.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest18`` () =
        let inputFile = """../../Examples/SAM/smokeTest18.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest19`` () =
        let inputFile = """../../Examples/SAM/smokeTest19.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest20`` () =
        let inputFile = """../../Examples/SAM/smokeTest20.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest21`` () =
        let inputFile = """../../Examples/SAM/smokeTest21.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest22`` () =
        let inputFile = """../../Examples/SAM/smokeTest22.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest23`` () =
        let inputFile = """../../Examples/SAM/smokeTest23.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest24`` () =
        let inputFile = """../../Examples/SAM/smokeTest24.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of smokeTest25`` () =
        let inputFile = """../../Examples/SAM/smokeTest25.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of nestedBlocks1`` () =
        let inputFile = """../../Examples/SAM/nestedBlocks1.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()

    [<Test>]
    let ``create dot graph of nestedBlocks2`` () =
        let inputFile = """../../Examples/SAM/nestedBlocks2.sam"""
        let ssaModel = SafetySharp.Workflow.runWorkflow_getState (readInputFileAndGenerateDotFile inputFile)
        ()