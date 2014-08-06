// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

namespace SafetySharp.Tests.Modelchecking.NuXmv.NuXmvExecuteTests

open NUnit.Framework
open SafetySharp.Tests
open SafetySharp.Tests.Modelchecking
open SafetySharp.Internal.Utilities
open SafetySharp.Internal.Modelchecking
open SafetySharp.Internal.Modelchecking.NuXmv

open SafetySharp.Tests.Modelchecking.NuXmv.Models

[<TestFixture>]
module NuXmvExecuteTests =

    [<Test>]
    let ``NuXmv is in PATH or in dependency folder`` () =
        let path = ExecuteNuXmv.FindNuXmv ()
        (path.Length > 0) =? true
        
    [<Test>]
    let ``NuXmv is runable and shows help`` () =
        let nuxmv = ExecuteNuXmv()
        nuxmv.IsNuXmvRunable () =? true
    
    [<Test>]
    let ``NuXmv starts in interactive mode`` () =
        let nuxmv = ExecuteNuXmv()
        nuxmv.StartNuXmvInteractive (-1) |> ignore //wait infinitely long
        let result = nuxmv.QuitNuXmvAndWaitForExit()
        ()
        
    [<Test>]
    let ``Shutdown of NuXmv can be forced`` () =
        let nuxmv = ExecuteNuXmv()
        nuxmv.StartNuXmvInteractive (-1) |> ignore //wait infinitely long
        System.Threading.Thread.Sleep (100)
        nuxmv.ForceShutdownNuXmv ()
        
    [<Test>]
    let ``An action associated with a spimple NuXmv-'echo'-Command gets executed after NuXmv has finished the command`` () =
        let nuxmv = ExecuteNuXmv()
        nuxmv.StartNuXmvInteractive (-1) |> ignore //wait infinitely long
        //nuxmv.ExecuteCommand(NuSMVCommand.Echo("verbose_level"),)

        true =? false
        
    [<Test>]
    let ``NuXmv doesn't read a syntactical wrong model file 1`` () =        
        let filename = "Modelchecking/NuXmv/wrong-syntax1.smv"
        let code = Models.``wrong-syntax1``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1)
        let outputTuple2 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandSequences.switchToXmlOutput)
        let outputTuple3 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandSequences.readModelAndBuildBdd filename)
        let outputTuple4 = nuxmv.QuitNuXmvAndWaitForExit()

        true =? false
        
    [<Test>]
    let ``NuXmv doesn't read a syntactical wrong model file 2`` () =        
        let filename = "Modelchecking/NuXmv/wrong-syntax2.smv"
        let code = Models.``wrong-syntax2``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        nuxmv.StartNuXmvInteractive (-1) |> ignore //wait infinitely long
        true =? false
        
    [<Test>]
    let ``NuXmv reads a file with a simple model`` () =
        true =? false
        
    [<Test>]
    let ``NuXmv returns a counterexample of an unsatisfied formula`` () =
        true =? false
        
    [<Test>]
    let ``NuXmv validates a satisfied formula`` () =
        true =? false
        
    [<Test>]
    let ``NuXmv validates two satisfied formulas`` () =
        true =? false
        


    open TestCase1
    
    [<Test>]
    let ``test transformed model`` () =
        let modelTransformer = MetamodelToNuXmv (testCase1Configuration)        
        let nuXmvCode = modelTransformer.transformConfiguration
        let nuXmvWriter = ExportNuXmvAstToFile()
        let nuXmvCodeString = nuXmvWriter.ExportNuXmvProgram nuXmvCode
        let filename = "Modelchecking/NuXmv/testcase1.smv"
        FileSystem.WriteToAsciiFile filename nuXmvCodeString

        let nuxmv = ExecuteNuXmv()
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1)
        let outputTuple2 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandSequences.switchToXmlOutput)
        let outputTuple3 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandSequences.readModelAndBuildBdd filename)
        let outputTuple4 = nuxmv.QuitNuXmvAndWaitForExit()
        let outputUnprocessed = nuxmv.ReturnUnprocessedOutput ()

        let outputTuples = [outputTuple1]@outputTuple2@outputTuple3@[outputTuple4]
        let resultTuples = outputTuples |> List.map nuxmv.ReturnCommandResult |> String.concat ""
        let result = resultTuples+outputUnprocessed

        result.Length > 0 =? true
        ()