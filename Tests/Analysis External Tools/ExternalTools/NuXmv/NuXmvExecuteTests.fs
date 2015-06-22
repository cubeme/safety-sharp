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

namespace SafetySharp.ExternalTools

open NUnit.Framework
open SafetySharp.Modelchecking
open SafetySharp
open SafetySharp.ExternalTools.Smv


// TODO: Improve test names

[<TestFixture>]
module NuXmvExecuteTestsBasic =

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
        let outputResultStart = nuxmv.StartNuXmvInteractive (-1) logFile //wait infinitely long
        let outputResultQuit = nuxmv.QuitNuXmvAndWaitForExit()
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
        let outputResultStart = nuxmv.StartNuXmvInteractive (-1) logFile |> ignore //wait infinitely long
        let outputTupleEcho = nuxmv.ExecuteAndIntepretCommand(NuSMVCommand.Echo("verbose_level"))
        let outputResultQuit = nuxmv.QuitNuXmvAndWaitForExit()
        outputTupleEcho.HasSucceeded =? true
        
    //[<Test>]
    //let ``shutdown of NuXmv is enforced after disposal of Execute-NuXmv-Object`` () =   
        


[<TestFixture>]
module NuXmvExecuteTestsWithPrebuildModels =

    [<Test>]
    let ``NuXmv doesn't read a file with an incomplete case distinction`` () =        
        let filename = "Modelchecking/NuXmv/incomplete-case-distinction.smv"
        let logFile = filename+".log"
        let code = SmvModels.``incomplete-case-distinction``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputResultStart = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nuxmv.QuitNuXmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? false
        outputResultBuildBdd.FailedCommand.IsSome =? true
        outputResultBuildBdd.FailedCommand.Value.Basic.Command =? (NuSMVCommand.BuildModel :> ICommand)
        
    [<Test>]
    let ``NuXmv doesn't read a file with an incomplete instantiation`` () =        
        let filename = "Modelchecking/NuXmv/incomplete-instantiation.smv"
        let logFile = filename+".log"
        let code = SmvModels.``incomplete-instantiation``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputResultStart = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nuxmv.QuitNuXmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? false
        outputResultBuildBdd.FailedCommand.IsSome =? true
        outputResultBuildBdd.FailedCommand.Value.Basic.Command =? (NuSMVCommand.FlattenHierarchy :> ICommand)
        
    // interpretation of check_fsm
    [<Test>]
    let ``NuXmv doesn't read a file which is not fully defined 1`` () =        
        let filename = "Modelchecking/NuXmv/not-fully-defined1.smv"
        let logFile = filename+".log"
        let code = SmvModels.``not-fully-defined1``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputResultStart = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTupleCheckFsm = nuxmv.ExecuteCommand NuSMVCommand.CheckFsm
        let outputResultQuit = nuxmv.QuitNuXmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? true
        outputTupleCheckFsm.HasSucceeded =? true
        let checkFsmResultInterpreted = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckFsm outputTupleCheckFsm
        checkFsmResultInterpreted.IsDeadlockFree =? false
        checkFsmResultInterpreted.IsTotal =? false

        
    // interpretation of check_fsm
    [<Test>]
    let ``NuXmv doesn't read a file which is not fully defined 2`` () =        
        let filename = "Modelchecking/NuXmv/not-fully-defined2.smv"
        let logFile = filename+".log"
        let code = SmvModels.``not-fully-defined2``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputResultStart = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTupleCheckFsm = nuxmv.ExecuteCommand NuSMVCommand.CheckFsm
        let outputResultQuit = nuxmv.QuitNuXmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? true
        outputTupleCheckFsm.HasSucceeded =? true
        let checkFsmResultInterpreted = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckFsm outputTupleCheckFsm
        checkFsmResultInterpreted.IsDeadlockFree =? true
        checkFsmResultInterpreted.IsTotal =? false


    // interpretation of check_fsm
    [<Test>]
    let ``NuXmv reads a file which is fully defined`` () =        
        let filename = "Modelchecking/NuXmv/fully-defined.smv"
        let logFile = filename+".log"
        let code = SmvModels.``fully-defined``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputResultStart = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTupleCheckFsm = nuxmv.ExecuteCommand NuSMVCommand.CheckFsm
        let outputResultQuit = nuxmv.QuitNuXmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? true
        outputTupleCheckFsm.HasSucceeded =? true
        let checkFsmResultInterpreted = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckFsm outputTupleCheckFsm
        checkFsmResultInterpreted.IsDeadlockFree =? true
        checkFsmResultInterpreted.IsTotal =? true


    [<Test>]
    let ``NuXmv doesn't read a syntactical wrong model file 1`` () =        
        let filename = "Modelchecking/NuXmv/wrong-syntax1.smv"
        let logFile = filename+".log"
        let code = SmvModels.``wrong-syntax1``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputResultStart = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nuxmv.QuitNuXmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? false
        outputResultBuildBdd.FailedCommand.IsSome =? true
        outputResultBuildBdd.FailedCommand.Value.Basic.Command =? (NuSMVCommand.FlattenHierarchy :> ICommand)
        
    [<Test>]
    let ``NuXmv doesn't read a syntactical wrong model file 2`` () =        
        let filename = "Modelchecking/NuXmv/wrong-syntax2.smv"
        let logFile = filename+".log"
        let code = SmvModels.``wrong-syntax2``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputTuple1 = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nuxmv.QuitNuXmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? false
        outputResultBuildBdd.FailedCommand.IsSome =? true
        outputResultBuildBdd.FailedCommand.Value.Basic.Command =? (NuSMVCommand.ReadModel(filename) :> ICommand)
        
    [<Test>]
    let ``NuXmv reads a file with a simple indeterminisitc model`` () =        
        let filename = "Modelchecking/NuXmv/simple-indeterministic.smv"
        let logFile = filename+".log"
        let code = SmvModels.``simple-indeterministic``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputResultStart = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nuxmv.QuitNuXmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? true
        outputResultBuildBdd.FailedCommand.IsSome =? false

        
    [<Test>]
    let ``NuXmv doesn't read a file which does not respect the range`` () =        
        let filename = "Modelchecking/NuXmv/range-not-respected.smv"
        let logFile = filename+".log"
        let code = SmvModels.``range-not-respected``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputResultStart = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nuxmv.QuitNuXmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? false
        outputResultBuildBdd.FailedCommand.IsSome =? true
        outputResultBuildBdd.FailedCommand.Value.Basic.Command =? (NuSMVCommand.BuildModel :> ICommand)

        
    [<Test>]
    let ``NuXmv reads a file with a simple determinisitc model`` () =        
        let filename = "Modelchecking/NuXmv/simple-deterministic.smv"
        let logFile = filename+".log"
        let code = SmvModels.``simple-deterministic``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputResultStart = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nuxmv.QuitNuXmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? true
        outputResultBuildBdd.FailedCommand.IsSome =? false

    let internal customCommand (str:string) =
        ({NuXmvCustomCommand.Command = str})

    [<Test>]
    let ``NuXmv validates valid ctl- and ltl-formulas and invariants`` () =
        let filename = "Modelchecking/NuXmv/simple-indeterministic.smv"
        let logFile = filename+".log"
        let code = SmvModels.``simple-indeterministic``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputResultStart = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        outputResultBuildBdd.HasSucceeded =? true
        let invariant = "(x=TRUE | x=FALSE)"
        let ctlProperty = sprintf "AG %s" invariant
        let outputAddPropertyCtl = nuxmv.ExecuteCommand (customCommand (sprintf """add_property -c -p "%s" -n "%s" """ ctlProperty "ctlProperty"))
        let ltlProperty = sprintf "G %s" invariant
        let outputAddPropertyLtl = nuxmv.ExecuteCommand (customCommand (sprintf """add_property -l -p "%s" -n "%s" """ ltlProperty "ltlProperty"))
        let outputAddPropertyInvariant = nuxmv.ExecuteCommand (customCommand (sprintf """add_property -i -p "%s" -n "%s" """ invariant "invariant"))
        outputAddPropertyCtl.HasSucceeded =? true
        outputAddPropertyLtl.HasSucceeded =? true
        outputAddPropertyInvariant.HasSucceeded =? true
        let outputCheckPropertyCtl = nuxmv.ExecuteCommand (customCommand (sprintf """check_property -P "%s" """ "ctlProperty"))
        let outputCheckPropertyLtl = nuxmv.ExecuteCommand (customCommand (sprintf """check_property -P "%s" """ "ltlProperty"))
        let outputCheckPropertyInvar = nuxmv.ExecuteCommand (customCommand (sprintf """check_property -P "%s" """ "invariant"))
        outputCheckPropertyCtl.HasSucceeded =? true
        outputCheckPropertyLtl.HasSucceeded =? true
        outputCheckPropertyInvar.HasSucceeded =? true        
        let interpretationCtl = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckCtlSpec outputCheckPropertyCtl
        let interpretationLtl = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckLtlSpec outputCheckPropertyLtl
        let interpretationInvar = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckInvar outputCheckPropertyInvar
        interpretationCtl.Result.IsSpecValid =? true
        interpretationLtl.Result.IsSpecValid =? true
        interpretationInvar.Result.IsSpecValid =? true
        let outputResultQuit = nuxmv.QuitNuXmvAndWaitForExit()
        ()
        
    [<Test>]
    let ``NuXmv finds counterexample for invalid ctl- and ltl-formulas and invariants with input as named property`` () =
        let filename = "Modelchecking/NuXmv/simple-deterministic.smv"
        let logFile = filename+".log"
        let code = SmvModels.``simple-deterministic``
        FileSystem.WriteToAsciiFile filename code
        let nuxmv = ExecuteNuXmv()
        let outputResultStart = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        outputResultBuildBdd.HasSucceeded =? true
        let invariant = "x=TRUE"
        let ctlProperty = sprintf "AG %s" invariant
        let outputAddPropertyCtl = nuxmv.ExecuteCommand (customCommand (sprintf """add_property -c -p "%s" -n "%s" """ ctlProperty "ctlProperty"))
        let ltlProperty = sprintf "G %s" invariant
        let outputAddPropertyLtl = nuxmv.ExecuteCommand (customCommand (sprintf """add_property -l -p "%s" -n "%s" """ ltlProperty "ltlProperty"))
        let outputAddPropertyInvariant = nuxmv.ExecuteCommand (customCommand (sprintf """add_property -i -p "%s" -n "%s" """ invariant "invariant"))
        outputAddPropertyCtl.HasSucceeded =? true
        outputAddPropertyLtl.HasSucceeded =? true
        outputAddPropertyInvariant.HasSucceeded =? true
        let outputCheckPropertyCtl = nuxmv.ExecuteCommand (customCommand (sprintf """check_property -P "%s" """ "ctlProperty"))
        let outputCheckPropertyLtl = nuxmv.ExecuteCommand (customCommand (sprintf """check_property -P "%s" """ "ltlProperty"))
        let outputCheckPropertyInvar = nuxmv.ExecuteCommand (customCommand (sprintf """check_property -P "%s" """ "invariant"))
        outputCheckPropertyCtl.HasSucceeded =? true
        outputCheckPropertyLtl.HasSucceeded =? true
        outputCheckPropertyInvar.HasSucceeded =? true
        let interpretationCtl = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckCtlSpec outputCheckPropertyCtl
        let interpretationLtl = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckLtlSpec outputCheckPropertyLtl
        let interpretationInvar = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckInvar outputCheckPropertyInvar
        interpretationCtl.Result.IsSpecInvalid =? true
        interpretationLtl.Result.IsSpecInvalid =? true
        interpretationInvar.Result.IsSpecInvalid =? true
        interpretationCtl.Result.HasCounterExample =? true
        interpretationLtl.Result.HasCounterExample =? true
        interpretationInvar.Result.HasCounterExample =? true
        // TODO: Check Traces
        let outputResultQuit = nuxmv.QuitNuXmvAndWaitForExit()        
        ()        
    
[<TestFixture>]
module NuXmvExecuteTestsWithAstModels =
    
    [<Test>]
    let todo () =
        ()
    (*
    
    [<Test>]
    let ``NuXmv finds counterexample for invalid ctl- and ltl-formulas and invariants with input as named property`` () =

    
    [<Test>]
    let ``NuXmv validates valid ctl- and ltl-formulas and invariants with direct input`` () =
    *)

(*
[<TestFixture>]
module NuXmvExecuteTestsWithModelFromSafetySharpMetamodel =

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
        let outputResultStart = nuxmv.StartNuXmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultBuildBddBasic = outputResultBuildBdd.GetBasicResultsOfAllCommand
        let outputResultQuit = nuxmv.QuitNuXmvAndWaitForExit()
        let outputUnprocessed = nuxmv.ReturnUnprocessedOutput ()

        let outputTuples = [outputResultStart]@outputResultBuildBddBasic@[outputResultQuit]
        let resultTuples = outputTuples |> List.map nuxmv.ReturnCommandResult |> String.concat ""
        let result = resultTuples+outputUnprocessed

        result.Length > 0 =? true
        ()
*)