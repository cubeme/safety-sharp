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

namespace SafetySharp.Internal.Modelchecking.NuXmv

// TODO:
//  - Ensure: stderr of the verbose result of a command is always associated to the correct command
//  - Introduce Cancelation Token. Read() and Mutexes() should be timed and check every second the status of the cancelationToken
//  - Tests for access from multiple Threads
//  - After NuXmv quits, ensure that this.CommandFinished () is called after last write into stdout and stderr

// be cautious:
//  - the command prompt does "nuXmv >" does not contain a line ending.
//  - this method avoids the problem with the newline
// Inspiration:
//  - http://alabaxblog.info/2013/06/redirectstandardoutput-beginoutputreadline-pattern-broken/
//  - https://gist.github.com/alabax/11353282

// Event Wait Handles:
// -  http://www.albahari.com/threading/part2.aspx#_Signaling_with_Event_Wait_Handles

[<RequireQualifiedAccess>]
type internal NuXmvCurrentTechniqueForVerification =
    | NotDetermined
    | SmtMode
    | BddMode
    
type internal INuXmvCommandResult =
    interface
        abstract member Basic : NuXmvCommandResultBasic
    end

and internal NuXmvCommandResultBasic = {
    Command: ICommand;
    Stderr : string;
    Stdout : string;
}   with
        interface INuXmvCommandResult with
            member this.Basic = this

(*
type internal NuXmvCommandResultFormula = {
    Command: ICommand;
    Stderr : string;
    Stdout : string;
}
*)

type internal NuXmvInterpretedResult =
    | AllSuccessful of Successful:NuXmvCommandResultBasic list
    | OneFailed of Successful:NuXmvCommandResultBasic list * Failed:NuXmvCommandResultBasic
    with
        member this.HasSucceeded () =
            match this with
                | AllSuccessful (_) -> true
                | OneFailed (_,_) -> false
        member this.FailedCommand () =
            match this with
                | AllSuccessful (_) -> None
                | OneFailed (_,failed) -> Some(failed)
        member this.GetResultsOfSuccessfulCommands () =
            match this with
                | AllSuccessful (successful) -> successful
                | OneFailed (successful,_) -> successful
        member this.GetResultsOfAllCommand () =
            match this with
                | AllSuccessful (successful) -> successful
                | OneFailed (successful,failed) -> successful@[failed]
    end

                    


type internal ExecuteNuXmv() =
    let commandToString = ExportCommandsToString ()

    
    let commandActiveMutex = new System.Threading.Mutex()
    let commandFinished = new System.Threading.AutoResetEvent (false);
    let stdoutReadyForNextRead = new System.Threading.AutoResetEvent (false);
    let mutable activeCommand : ICommand option =  None
    let mutable lastCommandResult : NuXmvCommandResultBasic option = None

    let mutable currentTechniqueForVerification = NuXmvCurrentTechniqueForVerification.NotDetermined
    let mutable currentModeOfProgram = NuXmvModeOfProgramm.NotStarted
    
    let stdoutCurrentLine = new System.Text.StringBuilder()
    let mutable stdoutPromptPossible = true
    let stdoutOutputBuffer = new System.Text.StringBuilder ()
    let stderrOutputBuffer = new System.Text.StringBuilder ()
    
    let mutable processOutputReader : System.Threading.Tasks.Task = null
    let mutable processErrorReader : System.Threading.Tasks.Task = null
    let mutable processWaiter : System.Threading.Tasks.Task<bool> = null
    let proc = new System.Diagnostics.Process()
    
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
        let candidates = candidatesManual @ candidatesOfPath
        match candidates |> Seq.tryFind tryCandidate with
            | Some(filename) -> filename
            | None -> failwith "Please add NuXmv installation folder into PATH or copy NuXmv-executable into the dependency folder. You can download NuXmv from http://nuxmv.fbk.eu"
        
    member this.TaskReadStderr () : System.Threading.Tasks.Task =
        System.Threading.Tasks.Task.Factory.StartNew(
            fun () -> 
                // http://msdn.microsoft.com/en-us/library/ath1fht8(v=vs.110).aspx
                let mutable endReached = false
                while endReached <> true do
                    let newChar = proc.StandardError.Read()
                    if newChar = -1 then
                        endReached <- true
                    else
                        let newChar = (char newChar)
                        stderrOutputBuffer.Append newChar |> ignore
                ()
        )

    member this.StdoutEndCurrentLine () =
        stdoutOutputBuffer.Append stdoutCurrentLine |> ignore
        stdoutCurrentLine.Clear() |> ignore
        stdoutPromptPossible <- true

    member this.FinishCommand () =        
        let newFinishedCommand = {
            NuXmvCommandResultBasic.Command = activeCommand.Value;
            NuXmvCommandResultBasic.Stdout = stdoutOutputBuffer.ToString();
            NuXmvCommandResultBasic.Stderr = stderrOutputBuffer.ToString();
        }
        lastCommandResult <-  Some(newFinishedCommand)
        activeCommand <- None
        stdoutOutputBuffer.Clear() |> ignore
        stderrOutputBuffer.Clear() |> ignore
        commandFinished.Set() |> ignore

    member this.TaskReadStdout () : System.Threading.Tasks.Task =
        // Note: This code assumes that the actual output of a command never contains
        // the prompt-string in one of its line beginnings!!! So it is kind of a hack.
        let checkIfActiveCommandFinished (character:char) (position:int) =
            let promptString = "nuXmv > "
            let updatePromptPossible ()=
                //position is 0-based
                if stdoutPromptPossible = false then
                    ()
                else
                    if position >= promptString.Length  then
                        stdoutPromptPossible <- false
                    else
                        let characterInPrompt = promptString.Chars(position)
                        if character <> characterInPrompt then
                            stdoutPromptPossible <- false
            updatePromptPossible ()
            let isPrompt : bool =
                stdoutPromptPossible && position = promptString.Length-1
            if isPrompt && activeCommand.IsSome then
                this.FinishCommand ()
                stdoutCurrentLine.Clear () |> ignore //get rid of the prompt
                stdoutReadyForNextRead.WaitOne() |> ignore

        System.Threading.Tasks.Task.Factory.StartNew(
            fun () -> 
                // http://msdn.microsoft.com/en-us/library/ath1fht8(v=vs.110).aspx
                let mutable endReached = false
                while endReached <> true do
                    let newChar = proc.StandardOutput.Read()
                    if newChar = -1 then
                        endReached <- true
                    let newChar = (char newChar)
                    if newChar = '\n' then
                        stdoutCurrentLine.Append newChar |> ignore
                        this.StdoutEndCurrentLine ()
                    else
                        stdoutCurrentLine.Append newChar |> ignore
                        checkIfActiveCommandFinished newChar (stdoutCurrentLine.Length - 1)
                ()
        )

    member this.TaskWaitForEnd (timeInMs:int) : System.Threading.Tasks.Task<bool> =
        System.Threading.Tasks.Task<bool>.Factory.StartNew(
            fun () ->
                if timeInMs > 0 then
                    let result = proc.WaitForExit(timeInMs)
                    //TODO: Should we first wait for [processOutputReader,processErrorReader] to ensure that
                    //      every output is attatched to the last command????
                    this.FinishCommand ()
                    result
                else
                    proc.WaitForExit()
                    //TODO: Should we first wait for [processOutputReader,processErrorReader] to ensure that
                    //      every output is attatched to the last command????
                    this.FinishCommand ()
                    true
        )
    
    member this.ExecuteCommand (command:ICommand) : NuXmvCommandResultBasic =
        // if a command is currently executing, wait
        commandActiveMutex.WaitOne() |> ignore
        
        activeCommand <- Some(command)
        this.StdoutEndCurrentLine()
        // NuXmv uses GNU readline and accepts commands from it. So it might be necessary to strip anything
        // which might be a control word of GNU readline out of the input-stream
        proc.StandardInput.WriteLine(commandToString.ExportICommand command) 

        commandFinished.WaitOne() |> ignore
        let result = lastCommandResult.Value
        
        stdoutReadyForNextRead.Set() |> ignore
        commandActiveMutex.ReleaseMutex()

        result

    
    // return Task, which can be awaited for
    member this.ExecuteCommandAsync (command:ICommand) : System.Threading.Tasks.Task<NuXmvCommandResultBasic> =
        System.Threading.Tasks.Task.Factory.StartNew(
            fun () -> this.ExecuteCommand command
        )
        
    member this.ExecuteCommandSequence (commands:ICommand list) =
        commands |> List.map (fun command -> (this.ExecuteCommand command))
        
    member this.ExecuteCommandString (command:string) =
        this.ExecuteCommand {NuXmvCustomCommand.Command = command};

    member this.IsNuXmvRunable () : bool =
        use proc = new System.Diagnostics.Process()        
        proc.StartInfo.Arguments <- commandToString.ExportNuXmvCommandLine NuXmvHelpfulCommandSequences.commandLineHelp
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
        // error codes are defined in src/cinit/cinitData.c
        // under windows there are no negative values. Thus exit code -1 becomes 255 (2-complement)
        match exitCode with
            | 0 -> true
            | 255 -> false
            | 2 -> true //help
            | _ -> false


    member this.StartNuXmvInteractive (timeInMs:int) : NuXmvCommandResultBasic =
        let initialCommand = NuXmvStartedCommand() :> ICommand
        activeCommand<-Some(initialCommand) 
        commandActiveMutex.WaitOne() |> ignore
        
        // TODO: check if already started (use expectedModeOfProgramAfterQueue)
        proc.StartInfo.Arguments <- commandToString.ExportNuXmvCommandLine NuXmvHelpfulCommandSequences.commandLineStart
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

        commandFinished.WaitOne() |> ignore
        let result = lastCommandResult        
        stdoutReadyForNextRead.Set() |> ignore
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
        // match exitCode with
        //     | 0 -> true
        //     | 255 -> false
        //     | 2 -> true //help
        //     | _ -> false
        //     | 0 -> Successful(stdoutOutputBuffer.ToString(), stderrOutputBuffer.ToString())
        //     | _ -> Failed(stdoutOutputBuffer.ToString(), stderrOutputBuffer.ToString())        


    //////////////////////////////
    // Interpreted Commands below
    /////////////////////////////

    (*
    member this.ReadModelBuildBddWithInterpretation () : NuXmvInterpretedResult =
        ()
        let outputTuple2 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandSequences.switchToXmlOutput)
        let outputTuple3 = nuxmv.ExecuteCommandSequence (NuXmvHelpfulCommandSequences.readModelAndBuildBdd filename)
        NuXmvInterpretedResult

    *)

        
    //////////////////////////////
    // Debugging helpers
    /////////////////////////////
        
    member this.ReturnCommandResult (entry:INuXmvCommandResult) : string = 
        let stringBuilder = new System.Text.StringBuilder()
        stringBuilder.AppendLine ((commandToString.ExportICommand entry.Basic.Command)) |> ignore
        stringBuilder.AppendLine ("stdout:\n" + entry.Basic.Stdout) |> ignore
        stringBuilder.AppendLine ("stderr:\n" + entry.Basic.Stderr) |> ignore
        stringBuilder.AppendLine "==========" |> ignore
        stringBuilder.ToString()
    
    member this.ReturnUnprocessedOutput () : string =
        let stringBuilder = new System.Text.StringBuilder()
        let printUnprocessed () : unit =
            stringBuilder.AppendLine "unprogressed" |> ignore
            stringBuilder.AppendLine ("stdout-line-buffer:\n" + stdoutCurrentLine.ToString() ) |> ignore
            stringBuilder.AppendLine ("stdout-buffer:\n" + stdoutOutputBuffer.ToString()) |> ignore
            stringBuilder.AppendLine ("stderr-buffer:\n" + stderrOutputBuffer.ToString()) |> ignore
            stringBuilder.AppendLine "==========" |> ignore
        let printActiveCommand () : unit =
            if activeCommand.IsSome then
                stringBuilder.AppendLine ("current Command:\n" + (commandToString.ExportICommand activeCommand.Value)) |> ignore
            else
                stringBuilder.AppendLine ("current Command:\n ---- ") |> ignore
            stringBuilder.AppendLine "==========" |> ignore
        let printCommandInQueue (number:int) (command:ICommand) : unit =
            stringBuilder.AppendLine ("Command " + (string number) + ":\n"+ (commandToString.ExportICommand command)) |> ignore
        //commandQueueResults |> Seq.iter printEntry
        printUnprocessed ()
        printActiveCommand ()
        //commandQueueToProcess |> Seq.iteri printCommandInQueue
        stringBuilder.ToString()