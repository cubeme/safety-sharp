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

namespace SafetySharp.Analysis.Modelchecking.NuXmv

// TODO:
//  - Introduce Cancellation Token. Read() and Mutexes() should be timed and check every second the status of the cancelationToken
// Source of Inspiration:
//  - http://alabaxblog.info/2013/06/redirectstandardoutput-beginoutputreadline-pattern-broken/
//  - https://gist.github.com/alabax/11353282
//  - http://www.codeproject.com/Articles/170017/Solving-Problems-of-Monitoring-Standard-Output-and
//  - http://stackoverflow.com/questions/1420965/redirect-stdout-and-stderr-to-a-single-file
//  - http://msdn.microsoft.com/en-us/library/windows/desktop/ms682075(v=vs.85).aspx
//  - http://msdn.microsoft.com/en-us/library/ath1fht8(v=vs.110).aspx
// -  http://www.albahari.com/threading/part2.aspx#_Signaling_with_Event_Wait_Handles

// for a fixed version of NuXmv, where "set nusmv_stdout" and "set nusmv_stderr" works, output
// could be redirected to the same file and this file could be read.


// idea:
// * after each command an 'echo -2 nuXmv finished last command' is appended
//   using 'set autoexec "echo -2 nuXmv finished last command"'
//   command finishes, when the stdout "nuXmv > " appears and
//   the stderr prompt was shown. Thus we can ensure that both stderr and stdout
//   were parsed until their end
// * commands can also be separated by ";" so using
//   'set autoexec "echo nuXmv finished last command; echo -2 nuXmv finished last command"'
//   could also be used as separation between two commands
// * Stdout-Thread waits for Stderr-Thread
//   ExecuteCommand-Thread waits for Stdout-Thread 
//   We assume after a "nuXmv finished last command" nothing else is written into each Buffer
//   until a new command is executed
// be cautious:
//  - the command prompt does "nuXmv >" does not contain a line ending.
//  - this method avoids the problem with the newline
//  - Ensure: stderr of the verbose result of a command is always associated to the correct command (race condition, actually a problem)
//  - some commands like "go" are actually chains of commands (go is a shorthand for 5 commands)
//    "autoexec" thus executes the "echo"-Command 5 times. Either use something which looks for the prompt
//    in stdout again (this time with a counter) or forbid chained-Commands to correctly determine the end of a command

// Execution of Threads (usually without any error):
//         Startup-Phase                                                                                                                                                                                                                 ┆  Command-Phase                                                                                                                                                      ┆ Shutdown-Phase                                                                                                                                                                                                ┆
//       Start ─── call StartNuXmvInteractive ────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────  stdoutAndCommandFinishedBlocker.WaitOne ─────┆─ call ExecuteCommand ────────────────────────────────────────────────────────────────────────────────────────────── stdoutAndCommandFinishedBlocker.WaitOne ────────┆─ call QuitNuXmvAndWaitForExit ───────────────────────────────────────────────────────────────────────────────────  stdoutAndCommandFinishedBlocker.WaitOne ─ wait for end of the three threads below ─────────┆─ ...
//                        ├─ new thread TaskReadStdout ─ TaskReadStdout.newLine* ─ command-finished-token in stdout found ──────── stderrFinishedBlocker.WaitOne  ─── stdoutAndCommandFinishedBlocker.Set ───────────────────────────────┆─ TaskReadStdout.newLine* ─── command-finished-token in stdout found ──────── stderrFinishedBlocker.WaitOne  ─── stdoutAndCommandFinishedBlocker.Set ────────────────┆─────── read StandardOutput.EndOfStream ─ set NuXmvModeOfProgramm.Terminated ─ stderrFinishedBlocker.WaitOne ─  stdoutAndCommandFinishedBlocker.Set ─⊸                                                         ┆
//                        ├─ new thread TaskReadStderr ─ TaskReadStderr.newLine* ─ command-finished-token in stderr found ── stderrFinishedBlocker.Set ──────────────────────────────────────────────────────────────────────────────────┆─ TaskReadStderr.newline* ─── command-finished-token in stderr found ── stderrFinishedBlocker.Set ───────────────────────────────────────────────────────────────────┆──────────────────────────────────────── read StandardError.EndOfStream ── stderrFinishedBlocker.Set ─⊸                                                                                                        ┆
//                        └─ new thread TaskWaitForEnd ─ start to wait for process end ──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┆─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┆────────── process ended ───⊸                                                                                                                                                                                  ┆
//
// Execution of Threads (with one unsuccessful command which leads to a shutdown):
//         Startup-Phase                                                                                                                                                                                                                 ┆  Command-Phase            ┆ Shutdown-Phase                                                                                                                                                ┆
//       Start ─── call StartNuXmvInteractive ────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────  stdoutAndCommandFinishedBlocker.WaitOne ─────┆─ call ExecuteCommand ─────┆───────────────────────────────────────────────────────────────────────────────────────────────────────────────────── stdoutAndCommandFinishedBlocker.WaitOne ─┆─ ...
//                        ├─ new thread TaskReadStdout ─ TaskReadStdout.newLine* ─ command-finished-token in stdout found ──────── stderrFinishedBlocker.WaitOne  ─── stdoutAndCommandFinishedBlocker.Set ───────────────────────────────┆─ TaskReadStdout.newLine* ─┆─────── read StandardOutput.EndOfStream ─ set NuXmvModeOfProgramm.Terminated ─ stderrFinishedBlocker.WaitOne ─  stdoutAndCommandFinishedBlocker.Set ─⊸         ┆
//                        ├─ new thread TaskReadStderr ─ TaskReadStderr.newLine* ─ command-finished-token in stderr found ── stderrFinishedBlocker.Set ──────────────────────────────────────────────────────────────────────────────────┆─ TaskReadStderr.newline* ─┆──────────────────────────────────────── read StandardError.EndOfStream ── stderrFinishedBlocker.Set ─⊸                                                        ┆
//                        └─ new thread TaskWaitForEnd ─ start to wait for process end ──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┆───────────────────────────┆────────── process ended ───⊸                                                                                                                                  ┆
// Remark: Unicode characters for visualization found on http://shapecatcher.com/unicode/block/Box_Drawing/


[<RequireQualifiedAccess>]
type internal NuXmvCurrentTechniqueForVerification =
    | NotDetermined
    | SmtMode
    | BddMode
    
                    


type internal ExecuteNuXmv() =    
    let commandActiveMutex = new System.Threading.Mutex()
    let stdoutAndCommandFinishedBlocker = new System.Threading.AutoResetEvent (false);
    let stderrFinishedBlocker = new System.Threading.AutoResetEvent (false);
    let mutable activeCommand : ICommand option =  None
    let mutable lastCommandResult : NuXmvCommandResultBasic option = None

    let mutable currentTechniqueForVerification = NuXmvCurrentTechniqueForVerification.NotDetermined
    let mutable currentModeOfProgram = NuXmvModeOfProgramm.NotStarted
    
    let stdoutOutputBuffer = new System.Text.StringBuilder ()
    let stderrOutputBuffer = new System.Text.StringBuilder ()
    
    let mutable processOutputReader : System.Threading.Tasks.Task = null
    let mutable processErrorReader : System.Threading.Tasks.Task = null
    let mutable processWaiter : System.Threading.Tasks.Task<bool> = null
    let proc = new System.Diagnostics.Process()
    
    let commandEndingStringStdout = "nuXmv finished last command stdout"
    let commandEndingStringStderr = "nuXmv finished last command stderr"
    let promptString = "nuXmv > "
    
    ///////////////////////////////////////////////////
    // NuXmv-Process and Interactive Console Management
    ///////////////////////////////////////////////////

    static member FindNuXmv (): string =
        let tryCandidate (filename:string) : bool =
            System.IO.File.Exists filename
        let candidatesManual = [
            "..\\..\\..\\..\\Dependencies\\NuXmv.exe";
        ]
        let candidatesOfPath =
            let paths=System.Environment.GetEnvironmentVariable("PATH").Split(';')
            paths |> Array.map (fun path -> System.IO.Path.Combine(path,"NuXmv.exe"))
                  |> Array.toList
        let candidateOfNuXmvPath =
            let path=System.Environment.GetEnvironmentVariable("NUXMV_DIR")
            if path = null then
                []
            else
                [System.IO.Path.Combine(path,"NuXmv.exe")]
        let candidates = candidateOfNuXmvPath @ candidatesManual @ candidatesOfPath
        match candidates |> Seq.tryFind tryCandidate with
            | Some(filename) -> filename
            | None -> failwith "Please add NuXmv installation folder into PATH\n or set the environmental variable NUXMV_PATH\n or copy NuXmv-executable into the dependency folder. You can download NuXmv from http://nuxmv.fbk.eu"
        
    member this.TaskReadStderr () : System.Threading.Tasks.Task =
        System.Threading.Tasks.Task.Factory.StartNew(
            fun () -> 
                // http://msdn.microsoft.com/en-us/library/system.io.streamreader.readline(v=vs.110).aspx
                while proc.StandardError.EndOfStream <> true  do
                    let newLine = proc.StandardError.ReadLine()
                    if newLine.StartsWith commandEndingStringStderr then
                        stderrOutputBuffer.AppendLine newLine |> ignore  //remove, if marker should not appear in stderr
                        stderrFinishedBlocker.Set () |> ignore
                    else
                        stderrOutputBuffer.AppendLine newLine |> ignore
                stderrFinishedBlocker.Set () |> ignore
        )
                
    member this.TaskReadStdout () : System.Threading.Tasks.Task =
        let FinishCommandAndReleaseBlocker () =
            if activeCommand.IsSome then 
                let newFinishedCommand = {
                    NuXmvCommandResultBasic.Command = activeCommand.Value;
                    NuXmvCommandResultBasic.Stdout = stdoutOutputBuffer.ToString();
                    NuXmvCommandResultBasic.Stderr = stderrOutputBuffer.ToString();
                    NuXmvCommandResultBasic.Failure = None; //Assume no failure occurred. If a failure occurred, ExecuteCommand detects it and corrects the result
                }
                lastCommandResult <-  Some(newFinishedCommand)
                activeCommand <- None
                stdoutOutputBuffer.Clear() |> ignore
                stderrOutputBuffer.Clear() |> ignore
                stdoutAndCommandFinishedBlocker.Set() |> ignore
            else
                // TODO: An exception is sometimes thrown here (System.NullReferenceException when Task is invoked)
                // TODO: It seems there is a race condition, this should never occur. In debug-mode sometimes the exception is thrown.
                //       Do further investigations
                failwith "When this is executed, activeCommand should contain a value"
                ()
        System.Threading.Tasks.Task.Factory.StartNew(
            fun () -> 
                let mutable needToRemovePromptFromCurrentLine = false //Before the first command is no prompt
                while proc.StandardOutput.EndOfStream <> true do
                    let newLine = proc.StandardOutput.ReadLine()
                    let newLineCleared =
                        // we need to clean out the prompt after a new command
                        // otherwise the check "newLine.StartsWith commandEndingStringStdout"
                        // is not true, when the prompt is before the marker
                        if needToRemovePromptFromCurrentLine && newLine.StartsWith(promptString) then
                            needToRemovePromptFromCurrentLine <- false
                            newLine.Remove(0,promptString.Length)
                        else
                            newLine
                    if newLineCleared.StartsWith commandEndingStringStdout then
                        stdoutOutputBuffer.AppendLine newLineCleared |> ignore //remove, if marker should not appear in stdout
                        stderrFinishedBlocker.WaitOne() |> ignore
                        FinishCommandAndReleaseBlocker ()
                        needToRemovePromptFromCurrentLine <- true
                        ()
                    else                        
                        stdoutOutputBuffer.AppendLine newLineCleared |> ignore
                // process definitively terminated here, because otherwise we wouldn't have received a EndOfStream-Token
                // we set the currentModeOfProgram here, because only here we can assure, that
                //    * we read everything from stderr
                //    * the main thread still waits in ExecuteCommand and there is no race-condition between the
                //      current command and a next command, which cannot be processed anymore, because nuXmv terminated.
                currentModeOfProgram<-NuXmvModeOfProgramm.Terminated //must occur before FinishCommandAndReleaseBlocker
                stderrFinishedBlocker.WaitOne() |> ignore
                FinishCommandAndReleaseBlocker ()
                ()
        )

    member this.TaskWaitForEnd (timeInMs:int) : System.Threading.Tasks.Task<bool> =
        System.Threading.Tasks.Task<bool>.Factory.StartNew(
            fun () ->
                if timeInMs > 0 then
                    let result = proc.WaitForExit(timeInMs)
                    result
                else
                    proc.WaitForExit()
                    true
        )
    
    member this.ExecuteCommand (command:ICommand) : NuXmvCommandResultBasic =
        // if a command is currently executing, wait
        // TODO: I think we can safely remove this mutex
        commandActiveMutex.WaitOne() |> ignore

        if currentModeOfProgram <> NuXmvModeOfProgramm.Terminated then
        
            activeCommand <- Some(command)
            // NuXmv uses GNU readline and accepts commands from it. So it might be necessary to strip anything
            // which might be a control word of GNU readline out of the input-stream
            proc.StandardInput.WriteLine(NuXmvCommandsToString.exportICommand command) 

            stdoutAndCommandFinishedBlocker.WaitOne() |> ignore

            let resultFailureUnconsidered = lastCommandResult.Value            
            let resultFailureConsidered =
                if currentModeOfProgram = NuXmvModeOfProgramm.Terminated then
                    // command was executed unsuccessfully (if it was not the quit-command)
                    // and lead to the termination of nuXmv
                    {
                        resultFailureUnconsidered with NuXmvCommandResultBasic.Failure = Some(CommandResultProcessingFailure.NotDeterminedYet)
                    }
                else
                    // command was executed successfully
                    resultFailureUnconsidered            
            
            commandActiveMutex.ReleaseMutex()

            resultFailureConsidered
        else
            commandActiveMutex.ReleaseMutex()            
            {
                NuXmvCommandResultBasic.Command=command;
                NuXmvCommandResultBasic.Stderr="";
                NuXmvCommandResultBasic.Stdout="";
                NuXmvCommandResultBasic.Failure=Some(CommandResultProcessingFailure.NuXmvShutdown);
            }

    
    // return Task, which can be awaited for
    member this.ExecuteCommandAsync (command:ICommand) : System.Threading.Tasks.Task<NuXmvCommandResultBasic> =
        System.Threading.Tasks.Task.Factory.StartNew(
            fun () -> this.ExecuteCommand command
        )
    
    member this.ExecuteAndIntepretCommand (command:ICommand) : INuXmvCommandResult =
        command |> this.ExecuteCommand
                |> NuXmvInterpretResult.interpretResult

    member this.ExecuteAndIntepretCommandSequence (commands:ICommand list) : NuXmvCommandResultsInterpreted =
        let rec processCommands (alreadySuccessfullyProcessedReverse:INuXmvCommandResult list) (commands) =
            match commands with
                | command :: tail ->
                    let result = this.ExecuteCommand command
                    let interpretedResult = NuXmvInterpretResult.interpretResult result
                    if interpretedResult.HasSucceeded then
                            processCommands (interpretedResult::alreadySuccessfullyProcessedReverse) tail
                    else
                        let successful = alreadySuccessfullyProcessedReverse |> List.rev
                        NuXmvCommandResultsInterpreted.OneFailed(successful,interpretedResult)
                | [] ->
                    let successful = alreadySuccessfullyProcessedReverse |> List.rev
                    NuXmvCommandResultsInterpreted.AllSuccessful(successful)        
        commands |> processCommands []
        
    member this.ExecuteCommandString (command:string) =
        this.ExecuteCommand {NuXmvCustomCommand.Command = command};

    member this.IsNuXmvRunable () : bool =
        use proc = new System.Diagnostics.Process()        
        proc.StartInfo.Arguments <- NuXmvCommandsToString.exportNuXmvCommandLine NuXmvHelpfulCommandsAndCommandSequences.commandLineHelp
        proc.StartInfo.FileName <- ExecuteNuXmv.FindNuXmv ()
        proc.StartInfo.WindowStyle <-  System.Diagnostics.ProcessWindowStyle.Hidden
        proc.StartInfo.CreateNoWindow <-  true
        proc.StartInfo.UseShellExecute <-  false
        proc.StartInfo.RedirectStandardOutput <-  false
        proc.StartInfo.RedirectStandardError <-  false
        proc.StartInfo.RedirectStandardInput <-  false
        proc.Start() |> ignore        
        proc.WaitForExit()
        let exitCode = proc.ExitCode
        // error codes are defined in <src/cinit/cinitData.c>
        // under windows there are no negative values. Thus exit code -1 becomes 255 (2-complement)
        match exitCode with
            | 0 -> true
            | 255 -> false
            | 2 -> true //help
            | _ -> false


    member this.StartNuXmvInteractive (timeInMs:int) (pathToLog:string) : NuXmvCommandResultBasic =
        let initialCommand = NuXmvStartedCommand() :> ICommand
        activeCommand<-Some(initialCommand) 
        commandActiveMutex.WaitOne() |> ignore
        
        // TODO: check if already started
        proc.StartInfo.Arguments <- NuXmvCommandsToString.exportNuXmvCommandLine (NuXmvHelpfulCommandsAndCommandSequences.commandLineStart)
        proc.StartInfo.FileName <- ExecuteNuXmv.FindNuXmv ()
        proc.StartInfo.WindowStyle <-  System.Diagnostics.ProcessWindowStyle.Hidden
        proc.StartInfo.CreateNoWindow <-  true
        proc.StartInfo.UseShellExecute <-  false
        proc.StartInfo.RedirectStandardOutput <-  true
        proc.StartInfo.RedirectStandardError <-  true
        proc.StartInfo.RedirectStandardInput <-  true

        proc.Start() |> ignore
        proc.StandardInput.AutoFlush <- true
        processOutputReader <- this.TaskReadStdout ()
        processErrorReader <- this.TaskReadStderr ()
        processWaiter <- this.TaskWaitForEnd (timeInMs)
        
        // this.ExecuteCommand cannot be used during initialization, so use StandardInput directly
        let quitOnFailure = NuXmvCommandsToString.exportICommand NuXmvHelpfulCommandsAndCommandSequences.enableOnFailureScriptQuits
        proc.StandardInput.WriteLine(quitOnFailure)
        let switchToXmlOutput = NuXmvCommandsToString.exportICommand NuXmvHelpfulCommandsAndCommandSequences.switchToXmlOutput
        proc.StandardInput.WriteLine(switchToXmlOutput)
        // indication must be the last command!!!
        let enableIndicationOfCommandEnd =
            let commandForAutoexec = sprintf "echo %s; echo -2 %s" commandEndingStringStdout commandEndingStringStderr
            NuXmvCommandsToString.exportICommand (NuXmvHelpfulCommandsAndCommandSequences.setAutoexec commandForAutoexec)            
        proc.StandardInput.WriteLine(enableIndicationOfCommandEnd) 

        stdoutAndCommandFinishedBlocker.WaitOne() |> ignore
        let result = lastCommandResult        
        commandActiveMutex.ReleaseMutex()
        result.Value
                           
                       
    member this.ForceShutdownNuXmv () =
        currentModeOfProgram <- NuXmvModeOfProgramm.Terminated
        proc.Kill()

    member this.QuitNuXmvAndWaitForExit () =
        let result = this.ExecuteCommand NuSMVCommand.Quit
        System.Threading.Tasks.Task.WaitAll(processOutputReader,processErrorReader,processWaiter)
        let exitCode = proc.ExitCode
        result      

                
    //////////////////////////////
    // Debugging helpers
    /////////////////////////////
        
    member this.ReturnCommandResult (entry:INuXmvCommandResult) : string = 
        let stringBuilder = new System.Text.StringBuilder()
        stringBuilder.AppendLine ((NuXmvCommandsToString.exportICommand entry.Basic.Command)) |> ignore
        stringBuilder.AppendLine ("stdout:\n" + entry.Basic.Stdout) |> ignore
        stringBuilder.AppendLine ("stderr:\n" + entry.Basic.Stderr) |> ignore
        stringBuilder.AppendLine "==========" |> ignore
        stringBuilder.ToString()
    
    member this.ReturnUnprocessedOutput () : string =
        let stringBuilder = new System.Text.StringBuilder()
        let printUnprocessed () : unit =
            stringBuilder.AppendLine "not progressed" |> ignore
            stringBuilder.AppendLine ("stdout-buffer:\n" + stdoutOutputBuffer.ToString()) |> ignore
            stringBuilder.AppendLine ("stderr-buffer:\n" + stderrOutputBuffer.ToString()) |> ignore
            stringBuilder.AppendLine "==========" |> ignore
        let printActiveCommand () : unit =
            if activeCommand.IsSome then
                stringBuilder.AppendLine ("current Command:\n" + (NuXmvCommandsToString.exportICommand activeCommand.Value)) |> ignore
            else
                stringBuilder.AppendLine ("current Command:\n ---- ") |> ignore
            stringBuilder.AppendLine "==========" |> ignore
        printUnprocessed ()
        printActiveCommand ()
        stringBuilder.ToString()