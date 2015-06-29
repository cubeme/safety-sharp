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
module NuSMV2ExecuteTestsBasic =

    [<Test>]
    let ``NuSMV is in PATH or in dependency folder`` () =
        let path = ExecuteNusmv2.FindNuSMV ()
        (path.Length > 0) =? true
        
    [<Test>]
    let ``NuSMV is runable and shows help`` () =
        let nusmv = ExecuteNusmv2 ()
        nusmv.IsToolRunable () =? true
    
    [<Test>]
    let ``NuSMV starts in interactive mode`` () =
        let nusmv = ExecuteNusmv2 ()
        let logFile = "startInteractiveMode.log"
        let outputResultStart = nusmv.StartSmvInteractive (-1) logFile //wait infinitely long
        let outputResultQuit = nusmv.QuitSmvAndWaitForExit()
        ()
        
    [<Test>]
    let ``Shutdown of NuSMV can be forced`` () =
        let nusmv = ExecuteNusmv2 ()
        let logFile = "forceShutdown.log"
        nusmv.StartSmvInteractive (-1) logFile |> ignore //wait infinitely long
        System.Threading.Thread.Sleep (100)
        nusmv.ForceShutdownSmv ()
        
    [<Test>]
    let ``An echo-command can be executed`` () =
        let nusmv = ExecuteNusmv2 ()
        let logFile = "echo.log"
        let outputResultStart = nusmv.StartSmvInteractive (-1) logFile |> ignore //wait infinitely long
        let outputTupleEcho = nusmv.ExecuteAndIntepretCommand(NuSMVCommand.Echo("verbose_level"))
        let outputResultQuit = nusmv.QuitSmvAndWaitForExit()
        outputTupleEcho.HasSucceeded =? true
        
    //[<Test>]
    //let ``shutdown of NuSMV is enforced after disposal of Execute-NuSMV-Object`` () =   
        


[<TestFixture>]
module NuSMV2ExecuteTestsWithPrebuildModels =
    let inputFile (testname:string) = """../../Examples/Smv/""" + testname

    [<Test>]
    let ``NuSMV doesn't read a file with an incomplete case distinction`` () =        
        let testname = SmvModels.``incomplete-case-distinction``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nusmv = ExecuteNusmv2 ()
        let outputResultStart = nusmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nusmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nusmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? false
        outputResultBuildBdd.FailedCommand.IsSome =? true
        outputResultBuildBdd.FailedCommand.Value.Basic.Command =? (NuSMVCommand.BuildModel :> ICommand)
        
    [<Test>]
    let ``NuSMV doesn't read a file with an incomplete instantiation`` () =        
        let testname = SmvModels.``incomplete-instantiation``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nusmv = ExecuteNusmv2 ()
        let outputResultStart = nusmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nusmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nusmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? false
        outputResultBuildBdd.FailedCommand.IsSome =? true
        outputResultBuildBdd.FailedCommand.Value.Basic.Command =? (NuSMVCommand.FlattenHierarchy :> ICommand)
        
    // interpretation of check_fsm
    [<Test>]
    let ``NuSMV doesn't read a file which is not fully defined 1`` () =        
        let testname = SmvModels.``not-fully-defined1``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nusmv = ExecuteNusmv2 ()
        let outputResultStart = nusmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nusmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTupleCheckFsm = nusmv.ExecuteCommand NuSMVCommand.CheckFsm
        let outputResultQuit = nusmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? true
        outputTupleCheckFsm.HasSucceeded =? true
        let checkFsmResultInterpreted = SmvInterpretResult.interpretResultOfNuSMVCommandCheckFsm outputTupleCheckFsm
        checkFsmResultInterpreted.IsDeadlockFree =? false
        checkFsmResultInterpreted.IsTotal =? false

        
    // interpretation of check_fsm
    [<Test>]
    let ``NuSMV doesn't read a file which is not fully defined 2`` () =        
        let testname = SmvModels.``not-fully-defined2``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nusmv = ExecuteNusmv2 ()
        let outputResultStart = nusmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nusmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTupleCheckFsm = nusmv.ExecuteCommand NuSMVCommand.CheckFsm
        let outputResultQuit = nusmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? true
        outputTupleCheckFsm.HasSucceeded =? true
        let checkFsmResultInterpreted = SmvInterpretResult.interpretResultOfNuSMVCommandCheckFsm outputTupleCheckFsm
        checkFsmResultInterpreted.IsDeadlockFree =? true
        checkFsmResultInterpreted.IsTotal =? false


    // interpretation of check_fsm
    [<Test>]
    let ``NuSMV reads a file which is fully defined`` () =        
        let testname = SmvModels.``fully-defined``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nusmv = ExecuteNusmv2 ()
        let outputResultStart = nusmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nusmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputTupleCheckFsm = nusmv.ExecuteCommand NuSMVCommand.CheckFsm
        let outputResultQuit = nusmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? true
        outputTupleCheckFsm.HasSucceeded =? true
        let checkFsmResultInterpreted = SmvInterpretResult.interpretResultOfNuSMVCommandCheckFsm outputTupleCheckFsm
        checkFsmResultInterpreted.IsDeadlockFree =? true
        checkFsmResultInterpreted.IsTotal =? true


    [<Test>]
    let ``NuSMV doesn't read a syntactical wrong model file 1`` () =        
        let testname = SmvModels.``wrong-syntax1``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nusmv = ExecuteNusmv2 ()
        let outputResultStart = nusmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nusmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nusmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? false
        outputResultBuildBdd.FailedCommand.IsSome =? true
        outputResultBuildBdd.FailedCommand.Value.Basic.Command =? (NuSMVCommand.FlattenHierarchy :> ICommand)
        
    [<Test>]
    let ``NuSMV doesn't read a syntactical wrong model file 2`` () =        
        let testname = SmvModels.``wrong-syntax2``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nusmv = ExecuteNusmv2 ()
        let outputTuple1 = nusmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nusmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nusmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? false
        outputResultBuildBdd.FailedCommand.IsSome =? true
        outputResultBuildBdd.FailedCommand.Value.Basic.Command =? (NuSMVCommand.ReadModel(filename) :> ICommand)
        
    [<Test>]
    let ``NuSMV reads a file with a simple indeterminisitc model`` () =        
        let testname = SmvModels.``simple-indeterministic``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nusmv = ExecuteNusmv2 ()
        let outputResultStart = nusmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nusmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nusmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? true
        outputResultBuildBdd.FailedCommand.IsSome =? false

        
    [<Test>]
    let ``NuSMV doesn't read a file which does not respect the range`` () =        
        let testname = SmvModels.``range-not-respected``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nusmv = ExecuteNusmv2 ()
        let outputResultStart = nusmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nusmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nusmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? false
        outputResultBuildBdd.FailedCommand.IsSome =? true
        outputResultBuildBdd.FailedCommand.Value.Basic.Command =? (NuSMVCommand.BuildModel :> ICommand)

        
    [<Test>]
    let ``NuSMV reads a file with a simple determinisitc model`` () =        
        let testname = SmvModels.``simple-deterministic``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nusmv = ExecuteNusmv2 ()
        let outputResultStart = nusmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nusmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        let outputResultQuit = nusmv.QuitSmvAndWaitForExit()
        outputResultBuildBdd.HasSucceeded =? true
        outputResultBuildBdd.FailedCommand.IsSome =? false

    let internal customCommand (str:string) =
        ({SmvCustomCommand.Command = str})

    [<Test>]
    let ``NuSMV validates valid ctl- and ltl-formulas and invariants`` () =
        let testname = SmvModels.``simple-indeterministic``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nusmv = ExecuteNusmv2 ()
        let outputResultStart = nusmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nusmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        outputResultBuildBdd.HasSucceeded =? true
        let invariant = "(x=TRUE | x=FALSE)"
        let ctlProperty = sprintf "AG %s" invariant
        let outputAddPropertyCtl = nusmv.ExecuteCommand (customCommand (sprintf """add_property -c -p "%s" -n "%s" """ ctlProperty "ctlProperty"))
        let ltlProperty = sprintf "G %s" invariant
        let outputAddPropertyLtl = nusmv.ExecuteCommand (customCommand (sprintf """add_property -l -p "%s" -n "%s" """ ltlProperty "ltlProperty"))
        let outputAddPropertyInvariant = nusmv.ExecuteCommand (customCommand (sprintf """add_property -i -p "%s" -n "%s" """ invariant "invariant"))
        outputAddPropertyCtl.HasSucceeded =? true
        outputAddPropertyLtl.HasSucceeded =? true
        outputAddPropertyInvariant.HasSucceeded =? true
        let outputCheckPropertyCtl = nusmv.ExecuteCommand (customCommand (sprintf """check_property -P "%s" """ "ctlProperty"))
        let outputCheckPropertyLtl = nusmv.ExecuteCommand (customCommand (sprintf """check_property -P "%s" """ "ltlProperty"))
        let outputCheckPropertyInvar = nusmv.ExecuteCommand (customCommand (sprintf """check_property -P "%s" """ "invariant"))
        outputCheckPropertyCtl.HasSucceeded =? true
        outputCheckPropertyLtl.HasSucceeded =? true
        outputCheckPropertyInvar.HasSucceeded =? true        
        let interpretationCtl = SmvInterpretResult.interpretResultOfNuSMVCommandCheckCtlSpec outputCheckPropertyCtl
        let interpretationLtl = SmvInterpretResult.interpretResultOfNuSMVCommandCheckLtlSpec outputCheckPropertyLtl
        let interpretationInvar = SmvInterpretResult.interpretResultOfNuSMVCommandCheckInvar outputCheckPropertyInvar
        interpretationCtl.Result.IsSpecValid =? true
        interpretationLtl.Result.IsSpecValid =? true
        interpretationInvar.Result.IsSpecValid =? true
        let outputResultQuit = nusmv.QuitSmvAndWaitForExit()
        ()
        
    [<Test>]
    let ``NuSMV finds counterexample for invalid ctl- and ltl-formulas and invariants with input as named property`` () =
        let testname = SmvModels.``simple-deterministic``
        let filename = inputFile testname
        let logFile = filename+".log"
        let nusmv = ExecuteNusmv2 ()
        let outputResultStart = nusmv.StartSmvInteractive (-1) logFile
        let outputResultBuildBdd = nusmv.ExecuteAndIntepretCommandSequence (SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
        outputResultBuildBdd.HasSucceeded =? true
        let invariant = "x=TRUE"
        let ctlProperty = sprintf "AG %s" invariant
        let outputAddPropertyCtl = nusmv.ExecuteCommand (customCommand (sprintf """add_property -c -p "%s" -n "%s" """ ctlProperty "ctlProperty"))
        let ltlProperty = sprintf "G %s" invariant
        let outputAddPropertyLtl = nusmv.ExecuteCommand (customCommand (sprintf """add_property -l -p "%s" -n "%s" """ ltlProperty "ltlProperty"))
        let outputAddPropertyInvariant = nusmv.ExecuteCommand (customCommand (sprintf """add_property -i -p "%s" -n "%s" """ invariant "invariant"))
        outputAddPropertyCtl.HasSucceeded =? true
        outputAddPropertyLtl.HasSucceeded =? true
        outputAddPropertyInvariant.HasSucceeded =? true
        let outputCheckPropertyCtl = nusmv.ExecuteCommand (customCommand (sprintf """check_property -P "%s" """ "ctlProperty"))
        let outputCheckPropertyLtl = nusmv.ExecuteCommand (customCommand (sprintf """check_property -P "%s" """ "ltlProperty"))
        let outputCheckPropertyInvar = nusmv.ExecuteCommand (customCommand (sprintf """check_property -P "%s" """ "invariant"))
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
        let outputResultQuit = nusmv.QuitSmvAndWaitForExit()        
        ()        
