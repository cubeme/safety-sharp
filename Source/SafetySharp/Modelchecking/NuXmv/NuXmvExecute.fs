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
//  - Ensure: If commandQueueToProcess is not empty and no Command is active, the next element in the queue is processed
//    Szenarios (What happens, if):
//     - ProcessNextQueueElement is called by two functions at the same time
//     - If one of those function calls is ignored (maybe called by an event) will the complete queue be processed in the future?
//  - Ensure: stderr of the verbose result of a command is always associated to the correct command


// be cautious:
//  - the command prompt does "nuXmv >" does not contain a line ending.
//  - this method avoids the problem with the newline
// Inspiration:
//  - http://alabaxblog.info/2013/06/redirectstandardoutput-beginoutputreadline-pattern-broken/
//  - https://gist.github.com/alabax/11353282


[<RequireQualifiedAccess>]
type internal NuXmvCurrentTechniqueForVerification =
    | NotDetermined
    | SmtMode
    | BddMode
    
type internal QueueCommand = {
    Command: ICommand;
    ActionsToExecuteAfterSuccess : System.Action list ;
}

type internal QueueCommandResult = {
    Command: ICommand;
    Stderr : string;
    Stdout : string;
}

type internal NuXmvResult =
    | Successful of string * string
    | Failed of string * string
    with
        member this.HasSucceeded with get () =
                                    match this with
                                        | Successful (_,_) -> true
                                        | Failed (_,_) -> false

type internal ExecuteNuXmv() =
    let commandToString = ExportCommandsToString ()

    let mutable activeCommand : QueueCommand option =  None
    let commandQueueToProcess = new System.Collections.Generic.Queue<QueueCommand>()
    let mutable expectedModeOfProgramAfterQueue = NuXmvModeOfProgramm.NotStarted
    let commandQueueResults = new System.Collections.Generic.List<QueueCommandResult>()

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

    member this.TaskReadStdout () : System.Threading.Tasks.Task =  
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
                let newFinishedCommand = {
                    QueueCommandResult.Command = activeCommand.Value.Command;
                    QueueCommandResult.Stdout = stdoutOutputBuffer.ToString();
                    QueueCommandResult.Stderr = stderrOutputBuffer.ToString();
                }
                commandQueueResults.Add newFinishedCommand
                activeCommand <- None
                stdoutOutputBuffer.Clear() |> ignore
                stderrOutputBuffer.Clear() |> ignore
                this.ProcessNextQueueElement()

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
                    proc.WaitForExit(timeInMs)
                else
                    proc.WaitForExit()
                    true
        )
            
    member this.AppendQueueCommand (command:QueueCommand) =
        // NuXmv uses GNU readline and accepts commands from it. So it might be necessary to strip them out from the input-stream
        // TODO: check if in valid state (use expectedModeOfProgramAfterQueue)
        if NuXmvCommandHelpers.isCommandExecutableInMode command.Command expectedModeOfProgramAfterQueue <> true then
            failwith "Command not executable in mode after queue"
        commandQueueToProcess.Enqueue(command)
        this.ProcessNextQueueElement ()
        
    member this.AppendQueueCommands (commands:QueueCommand list) =
        commands |> List.iter this.AppendQueueCommand

    member this.ExecuteCommand (command:ICommand) =
        let queueCommand = {
            QueueCommand.Command = command;
            QueueCommand.ActionsToExecuteAfterSuccess = [];
        }
        this.AppendQueueCommand(queueCommand)
        
    member this.ExecuteCommandSequence (commands:ICommand list) =
        commands |> List.iter this.ExecuteCommand
        
    member this.ExecuteCommandString (command:string) (actionsToExecuteAfterSuccess : System.Action list) =
        let queueCommand = {
            QueueCommand.Command = {NuXmvCustomCommand.Command = command};
            QueueCommand.ActionsToExecuteAfterSuccess = actionsToExecuteAfterSuccess;
        }
        this.AppendQueueCommand queueCommand

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


    member this.StartNuXmvInteractive (timeInMs:int) : unit =
        // TODO: check if already started (use expectedModeOfProgramAfterQueue)
        let initialCommand = 
            {
                QueueCommand.Command = NuXmvStartedCommand();
                QueueCommand.ActionsToExecuteAfterSuccess = [];
            }
        activeCommand<-Some(initialCommand)
        expectedModeOfProgramAfterQueue <- NuXmvModeOfProgramm.InitialOrReseted
                
              
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
        ()
                
    member this.ProcessNextQueueElement () =
        if activeCommand.IsSome then
            ()
        else
            if commandQueueToProcess.Count > 0 then
                let commandToExecute = commandQueueToProcess.Dequeue()
                activeCommand <- Some(commandToExecute)
                this.StdoutEndCurrentLine()
                proc.StandardInput.WriteLine(commandToString.ExportICommand commandToExecute.Command) 
            
                       
    member this.ForceShutdownNuXmv () =
        currentModeOfProgram <- NuXmvModeOfProgramm.Terminated
        proc.Kill()

    member this.QuitNuXmvAndWaitForExit () =
        this.ExecuteCommand NuSMVCommand.Quit
        System.Threading.Tasks.Task.WaitAll(processOutputReader,processErrorReader,processWaiter)

        let exitCode = proc.ExitCode
        ()
        // match exitCode with
        //     | 0 -> true
        //     | 255 -> false
        //     | 2 -> true //help
        //     | _ -> false
        //     | 0 -> Successful(stdoutOutputBuffer.ToString(), stderrOutputBuffer.ToString())
        //     | _ -> Failed(stdoutOutputBuffer.ToString(), stderrOutputBuffer.ToString())        

    member this.ReturnResults () : string =
        let stringBuilder = new System.Text.StringBuilder()
        let printEntry (entry:QueueCommandResult) : unit = 
            stringBuilder.AppendLine ((commandToString.ExportICommand entry.Command)) |> ignore
            stringBuilder.AppendLine ("stdout:\n" + entry.Stdout) |> ignore
            stringBuilder.AppendLine ("stderr:\n" + entry.Stderr) |> ignore
            stringBuilder.AppendLine "==========" |> ignore
        let printUnprogressed () : unit =
            stringBuilder.AppendLine "unprogressed" |> ignore
            stringBuilder.AppendLine ("stdout-line-buffer:\n" + stdoutCurrentLine.ToString() ) |> ignore
            stringBuilder.AppendLine ("stdout-buffer:\n" + stdoutOutputBuffer.ToString()) |> ignore
            stringBuilder.AppendLine ("stderr-buffer:\n" + stderrOutputBuffer.ToString()) |> ignore
            stringBuilder.AppendLine "==========" |> ignore
        let printActiveCommand () : unit =
            if activeCommand.IsSome then
                stringBuilder.AppendLine ("current Command:\n" + (commandToString.ExportICommand activeCommand.Value.Command)) |> ignore
            else
                stringBuilder.AppendLine ("current Command:\n ---- ") |> ignore
            stringBuilder.AppendLine "==========" |> ignore
        let printCommandInQueue (number:int) (command:QueueCommand) : unit =
            stringBuilder.AppendLine ("Command " + (string number) + ":\n"+ (commandToString.ExportICommand command.Command)) |> ignore
        commandQueueResults |> Seq.iter printEntry
        printUnprogressed ()
        printActiveCommand ()
        commandQueueToProcess |> Seq.iteri printCommandInQueue
        stringBuilder.ToString()