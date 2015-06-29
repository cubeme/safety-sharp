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

namespace SafetySharp.ExternalTools.Smv

open NUnit.Framework
open SafetySharp
open SafetySharp.ExternalTools.Smv


// TODO: Improve test names

[<TestFixture>]
module NuXmvExecuteTestsBasic =

    [<Test>]
    let ``NuXmv is in PATH or in dependency folder`` () =
        let path = ExecuteNuxmv.FindNuXmv ()
        (path.Length > 0) =? true
        
    [<Test>]
    let ``NuXmv is runable and shows help`` () =
        let nuxmv = ExecuteNuxmv()
        nuxmv.IsToolRunable () =? true
    
    [<Test>]
    let ``NuXmv starts in interactive mode`` () =
        let nuxmv = ExecuteNuxmv()
        let logFile = "startInteractiveMode.log"
        let outputResultStart = nuxmv.StartSmvInteractive (-1) logFile //wait infinitely long
        let outputResultQuit = nuxmv.QuitSmvAndWaitForExit()
        ()
        
    [<Test>]
    let ``Shutdown of NuXmv can be forced`` () =
        let nuxmv = ExecuteNuxmv()
        let logFile = "forceShutdown.log"
        nuxmv.StartSmvInteractive (-1) logFile |> ignore //wait infinitely long
        System.Threading.Thread.Sleep (100)
        nuxmv.ForceShutdownSmv ()
        
    [<Test>]
    let ``An echo-command can be executed`` () =
        let nuxmv = ExecuteNuxmv()
        let logFile = "echo.log"
        let outputResultStart = nuxmv.StartSmvInteractive (-1) logFile |> ignore //wait infinitely long
        let outputTupleEcho = nuxmv.ExecuteAndIntepretCommand(NuSMVCommand.Echo("verbose_level"))
        let outputResultQuit = nuxmv.QuitSmvAndWaitForExit()
        outputTupleEcho.HasSucceeded =? true
        
    //[<Test>]
    //let ``shutdown of NuXmv is enforced after disposal of Execute-NuXmv-Object`` () =   
        


[<TestFixture>]
module NuXmvExecuteTestsWithPrebuildModels =
    let inputFile (testname:string) = """../../Examples/Smv/""" + testname

    [<Test>]
    let ``NuXmv doesn't read a file with an incomplete case distinction`` () =        
        let testname = SmvModels.``incomplete-case-distinction``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nuxmv = ExecuteNuxmv()
        let outputResultStart = nuxmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nuxmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? false
        outputResultBuildBdd.FailedCommand.IsSome =? true
        outputResultBuildBdd.FailedCommand.Value.Basic.Command =? (NuSMVCommand.BuildModel :> ICommand)
        
    [<Test>]
    let ``NuXmv doesn't read a file with an incomplete instantiation`` () =        
        let testname = SmvModels.``incomplete-instantiation``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nuxmv = ExecuteNuxmv()
        let outputResultStart = nuxmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nuxmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? false
        outputResultBuildBdd.FailedCommand.IsSome =? true
        outputResultBuildBdd.FailedCommand.Value.Basic.Command =? (NuSMVCommand.FlattenHierarchy :> ICommand)
        
    // interpretation of check_fsm
    [<Test>]
    let ``NuXmv doesn't read a file which is not fully defined 1`` () =        
        let testname = SmvModels.``not-fully-defined1``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nuxmv = ExecuteNuxmv()
        let outputResultStart = nuxmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTupleCheckFsm = nuxmv.ExecuteCommand NuSMVCommand.CheckFsm
        let outputResultQuit = nuxmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? true
        outputTupleCheckFsm.HasSucceeded =? true
        let checkFsmResultInterpreted = SmvInterpretResult.interpretResultOfNuSMVCommandCheckFsm outputTupleCheckFsm
        checkFsmResultInterpreted.IsDeadlockFree =? false
        checkFsmResultInterpreted.IsTotal =? false

        
    // interpretation of check_fsm
    [<Test>]
    let ``NuXmv doesn't read a file which is not fully defined 2`` () =        
        let testname = SmvModels.``not-fully-defined2``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nuxmv = ExecuteNuxmv()
        let outputResultStart = nuxmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTupleCheckFsm = nuxmv.ExecuteCommand NuSMVCommand.CheckFsm
        let outputResultQuit = nuxmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? true
        outputTupleCheckFsm.HasSucceeded =? true
        let checkFsmResultInterpreted = SmvInterpretResult.interpretResultOfNuSMVCommandCheckFsm outputTupleCheckFsm
        checkFsmResultInterpreted.IsDeadlockFree =? true
        checkFsmResultInterpreted.IsTotal =? false


    // interpretation of check_fsm
    [<Test>]
    let ``NuXmv reads a file which is fully defined`` () =        
        let testname = SmvModels.``fully-defined``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nuxmv = ExecuteNuxmv()
        let outputResultStart = nuxmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTupleCheckFsm = nuxmv.ExecuteCommand NuSMVCommand.CheckFsm
        let outputResultQuit = nuxmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? true
        outputTupleCheckFsm.HasSucceeded =? true
        let checkFsmResultInterpreted = SmvInterpretResult.interpretResultOfNuSMVCommandCheckFsm outputTupleCheckFsm
        checkFsmResultInterpreted.IsDeadlockFree =? true
        checkFsmResultInterpreted.IsTotal =? true


    [<Test>]
    let ``NuXmv doesn't read a syntactical wrong model file 1`` () =        
        let testname = SmvModels.``wrong-syntax1``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nuxmv = ExecuteNuxmv()
        let outputResultStart = nuxmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nuxmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? false
        outputResultBuildBdd.FailedCommand.IsSome =? true
        outputResultBuildBdd.FailedCommand.Value.Basic.Command =? (NuSMVCommand.FlattenHierarchy :> ICommand)
        
    [<Test>]
    let ``NuXmv doesn't read a syntactical wrong model file 2`` () =        
        let testname = SmvModels.``wrong-syntax2``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nuxmv = ExecuteNuxmv()
        let outputTuple1 = nuxmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nuxmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? false
        outputResultBuildBdd.FailedCommand.IsSome =? true
        outputResultBuildBdd.FailedCommand.Value.Basic.Command =? (NuSMVCommand.ReadModel(filename) :> ICommand)
        
    [<Test>]
    let ``NuXmv reads a file with a simple indeterminisitc model`` () =        
        let testname = SmvModels.``simple-indeterministic``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nuxmv = ExecuteNuxmv()
        let outputResultStart = nuxmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nuxmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? true
        outputResultBuildBdd.FailedCommand.IsSome =? false

        
    [<Test>]
    let ``NuXmv doesn't read a file which does not respect the range`` () =        
        let testname = SmvModels.``range-not-respected``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nuxmv = ExecuteNuxmv()
        let outputResultStart = nuxmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nuxmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? false
        outputResultBuildBdd.FailedCommand.IsSome =? true
        outputResultBuildBdd.FailedCommand.Value.Basic.Command =? (NuSMVCommand.BuildModel :> ICommand)

        
    [<Test>]
    let ``NuXmv reads a file with a simple determinisitc model`` () =        
        let testname = SmvModels.``simple-deterministic``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nuxmv = ExecuteNuxmv()
        let outputResultStart = nuxmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nuxmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? true
        outputResultBuildBdd.FailedCommand.IsSome =? false

    let internal customCommand (str:string) =
        ({SmvCustomCommand.Command = str})

    [<Test>]
    let ``NuXmv validates valid ctl- and ltl-formulas and invariants`` () =
        let testname = SmvModels.``simple-indeterministic``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nuxmv = ExecuteNuxmv()
        let outputResultStart = nuxmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
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
        let interpretationCtl = SmvInterpretResult.interpretResultOfNuSMVCommandCheckCtlSpec outputCheckPropertyCtl
        let interpretationLtl = SmvInterpretResult.interpretResultOfNuSMVCommandCheckLtlSpec outputCheckPropertyLtl
        let interpretationInvar = SmvInterpretResult.interpretResultOfNuSMVCommandCheckInvar outputCheckPropertyInvar
        interpretationCtl.Result.IsSpecValid =? true
        interpretationLtl.Result.IsSpecValid =? true
        interpretationInvar.Result.IsSpecValid =? true
        let outputResultQuit = nuxmv.QuitSmvAndWaitForExit()
        ()
        
    [<Test>]
    let ``NuXmv finds counterexample for invalid ctl- and ltl-formulas and invariants with input as named property`` () =
        let testname = SmvModels.``simple-deterministic``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nuxmv = ExecuteNuxmv()
        let outputResultStart = nuxmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nuxmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
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
        let interpretationCtl = SmvInterpretResult.interpretResultOfNuSMVCommandCheckCtlSpec outputCheckPropertyCtl
        let interpretationLtl = SmvInterpretResult.interpretResultOfNuSMVCommandCheckLtlSpec outputCheckPropertyLtl
        let interpretationInvar = SmvInterpretResult.interpretResultOfNuSMVCommandCheckInvar outputCheckPropertyInvar
        interpretationCtl.Result.IsSpecInvalid =? true
        interpretationLtl.Result.IsSpecInvalid =? true
        interpretationInvar.Result.IsSpecInvalid =? true
        interpretationCtl.Result.HasCounterExample =? true
        interpretationLtl.Result.HasCounterExample =? true
        interpretationInvar.Result.HasCounterExample =? true
        // TODO: Check Traces
        let outputResultQuit = nuxmv.QuitSmvAndWaitForExit()        
        ()        
