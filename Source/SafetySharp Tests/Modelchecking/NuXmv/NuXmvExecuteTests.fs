﻿// The MIT License (MIT)
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

// TODO: Improve test names

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
        let logFile = "startInteractiveMode.log"
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1) logFile //wait infinitely long
        let outputTuple2 = nuxmv.QuitNuXmvAndWaitForExit()
        ()
        
    [<Test>]
    let ``Shutdown of NuXmv can be forced`` () =
        let nuxmv = ExecuteNuXmv()
        let logFile = "forceShutdown.log"
        nuxmv.StartNuXmvInteractive (-1) logFile |> ignore //wait infinitely long
        System.Threading.Thread.Sleep (100)
        nuxmv.ForceShutdownNuXmv ()
        
    [<Test>]
    let ``An echo-command can be executed`` () =
        let nuxmv = ExecuteNuXmv()
        let logFile = "echo.log"
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1) logFile |> ignore //wait infinitely long
        let outputTuple2 = nuxmv.ExecuteCommand(NuSMVCommand.Echo("verbose_level"))
        let outputTuple3 = nuxmv.QuitNuXmvAndWaitForExit()
        outputTuple2.Failure.IsNone =? true

        
    [<Test>]
    let ``NuXmv doesn't read a file with an incomplete case distinction`` () =        
        let filename = "Modelchecking/NuXmv/incomplete-case-distinction.smv"
        let logFile = filename+".log"
        let code = Models.``incomplete-case-distinction``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputTuple3 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTuple4 = nuxmv.QuitNuXmvAndWaitForExit()
        outputTuple3.HasSucceeded =? false
        outputTuple3.FailedCommand.IsSome =? true
        outputTuple3.FailedCommand.Value.Basic.Command =? (NuSMVCommand.FlattenHierarchy :> ICommand)
        
    [<Test>]
    let ``NuXmv doesn't read a file with an incomplete instantiation`` () =        
        let filename = "Modelchecking/NuXmv/incomplete-instantiation.smv"
        let logFile = filename+".log"
        let code = Models.``incomplete-instantiation``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputTuple3 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTuple4 = nuxmv.QuitNuXmvAndWaitForExit()
        outputTuple3.HasSucceeded =? false
        outputTuple3.FailedCommand.IsSome =? true
        outputTuple3.FailedCommand.Value.Basic.Command =? (NuSMVCommand.FlattenHierarchy :> ICommand)
        
    // interpretation of check_fsm
    [<Test>]
    let ``NuXmv doesn't read a file which is not fully defined 1`` () =        
        let filename = "Modelchecking/NuXmv/not-fully-defined1.smv"
        let logFile = filename+".log"
        let code = Models.``not-fully-defined1``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputTuple3 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTuple4 = nuxmv.QuitNuXmvAndWaitForExit()
        outputTuple3.HasSucceeded =? false
        outputTuple3.FailedCommand.IsSome =? true
        outputTuple3.FailedCommand.Value.Basic.Command =? (NuSMVCommand.FlattenHierarchy :> ICommand)

        
    // interpretation of check_fsm
    [<Test>]
    let ``NuXmv doesn't read a file which is not fully defined 2`` () =        
        let filename = "Modelchecking/NuXmv/not-fully-defined2.smv"
        let logFile = filename+".log"
        let code = Models.``not-fully-defined2``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputTuple3 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTuple4 = nuxmv.QuitNuXmvAndWaitForExit()
        outputTuple3.HasSucceeded =? false
        outputTuple3.FailedCommand.IsSome =? true
        outputTuple3.FailedCommand.Value.Basic.Command =? (NuSMVCommand.FlattenHierarchy :> ICommand)


    // interpretation of check_fsm
    [<Test>]
    let ``NuXmv read a file which is fully defined`` () =        
        let filename = "Modelchecking/NuXmv/fully-defined.smv"
        let logFile = filename+".log"
        let code = Models.``fully-defined``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputTuple3 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTuple4 = nuxmv.QuitNuXmvAndWaitForExit()
        outputTuple3.HasSucceeded =? false
        outputTuple3.FailedCommand.IsSome =? true
        outputTuple3.FailedCommand.Value.Basic.Command =? (NuSMVCommand.FlattenHierarchy :> ICommand)


    [<Test>]
    let ``NuXmv doesn't read a syntactical wrong model file 1`` () =        
        let filename = "Modelchecking/NuXmv/wrong-syntax1.smv"
        let logFile = filename+".log"
        let code = Models.``wrong-syntax1``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputTuple3 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTuple4 = nuxmv.QuitNuXmvAndWaitForExit()
        outputTuple3.HasSucceeded =? false
        outputTuple3.FailedCommand.IsSome =? true
        outputTuple3.FailedCommand.Value.Basic.Command =? (NuSMVCommand.FlattenHierarchy :> ICommand)
        
    [<Test>]
    let ``NuXmv doesn't read a syntactical wrong model file 2`` () =        
        let filename = "Modelchecking/NuXmv/wrong-syntax2.smv"
        let logFile = filename+".log"
        let code = Models.``wrong-syntax2``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputTuple3 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTuple4 = nuxmv.QuitNuXmvAndWaitForExit()
        outputTuple3.HasSucceeded =? false
        outputTuple3.FailedCommand.IsSome =? true
        outputTuple3.FailedCommand.Value.Basic.Command =? (NuSMVCommand.ReadModel(filename) :> ICommand)
        
    // for traces
    [<Test>]
    let ``NuXmv reads a file with a simple indeterminisitc model`` () =        
        let filename = "Modelchecking/NuXmv/simple-indeterministic.smv"
        let logFile = filename+".log"
        let code = Models.``simple-indeterministic``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputTuple3 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTuple4 = nuxmv.QuitNuXmvAndWaitForExit()
        outputTuple3.HasSucceeded =? true
        outputTuple3.FailedCommand.IsSome =? false

        
    [<Test>]
    let ``NuXmv doesn't read a file which does not respect the range`` () =        
        let filename = "Modelchecking/NuXmv/range-not-respected.smv"
        let logFile = filename+".log"
        let code = Models.``range-not-respected``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputTuple3 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTuple4 = nuxmv.QuitNuXmvAndWaitForExit()
        outputTuple3.HasSucceeded =? true
        outputTuple3.FailedCommand.IsSome =? false

        
    // for traces
    [<Test>]
    let ``NuXmv reads a file with a simple determinisitc model`` () =        
        let filename = "Modelchecking/NuXmv/simple-deterministic.smv"
        let logFile = filename+".log"
        let code = Models.``simple-deterministic``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputTuple3 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTuple4 = nuxmv.QuitNuXmvAndWaitForExit()
        outputTuple3.HasSucceeded =? true
        outputTuple3.FailedCommand.IsSome =? false
        
    (*
    [<Test>]
    let ``NuXmv returns a counterexample of an unsatisfied formula`` () =
        true =? false
        
    [<Test>]
    let ``NuXmv validates a satisfied formula`` () =
        true =? false
        
    [<Test>]
    let ``NuXmv validates two satisfied formulas`` () =
        true =? false

        
    [<Test>]
    let ``shutdown of NuXmv is enforced after disposal of Execute-NuXmv-Object`` () =   

    *)  


    open TestCase1
    
    [<Test>]
    let ``test transformed model`` () =
        let modelTransformer = MetamodelToNuXmv (testCase1Configuration)        
        let nuXmvCode = modelTransformer.transformConfiguration
        let nuXmvWriter = ExportNuXmvAstToFile()
        let nuXmvCodeString = nuXmvWriter.ExportNuXmvProgram nuXmvCode
        let filename = "Modelchecking/NuXmv/testcase1.smv"
        let logFile = filename+".log"
        FileSystem.WriteToAsciiFile filename nuXmvCodeString

        let nuxmv = ExecuteNuXmv()
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputTuples3 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTuples3Basic = outputTuples3.GetBasicResultsOfAllCommand
        let outputTuple4 = nuxmv.QuitNuXmvAndWaitForExit()
        let outputUnprocessed = nuxmv.ReturnUnprocessedOutput ()

        let outputTuples = [outputTuple1]@outputTuples3Basic@[outputTuple4]
        let resultTuples = outputTuples |> List.map nuxmv.ReturnCommandResult |> String.concat ""
        let result = resultTuples+outputUnprocessed

        result.Length > 0 =? true
        ()