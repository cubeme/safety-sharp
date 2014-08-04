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
//  - Ensure: If commandQueueToProcess is not empty, Processing is Followed by WaitingForInput. (Doesn't get stuck in WaitingForInput)
//    Szenarios (What happens, if):
//     - ProcessNextQueueElement is called by two functions at the same time
//     - If one of those function calls is ignored (maybe called by an event) will the complete queue be processed in the future?


(*
[<RequireQualifiedAccess>]
type internal NuXmvStateOfInput =
    | WaitingForInput
    | Processing
*)

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

    //let mutable currentStateOfInput = NuXmvStateOfInput.Processing
    let mutable currentTechniqueForVerification = NuXmvCurrentTechniqueForVerification.NotDetermined
    let mutable currentModeOfProgram = NuXmvModeOfProgramm.NotStarted
    
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
    
    (*
    old Method
    member this.stderrReceivedNewInput (dataReceivedEvArgs:System.Diagnostics.DataReceivedEventArgs) = 
        let newData = dataReceivedEvArgs.Data
        stderrOutputBuffer.Append newData |> ignore

    member this.stdoutReceivedNewInput (dataReceivedEvArgs:System.Diagnostics.DataReceivedEventArgs) = 
        let newData = dataReceivedEvArgs.Data
        if newData.StartsWith "nuXmv >" && activeCommand.IsSome then
            let newFinishedCommand = {
                QueueCommandResult.Command = activeCommand.Value.Command;
                QueueCommandResult.Stdout = stdoutOutputBuffer.ToString();
                QueueCommandResult.Stderr = stderrOutputBuffer.ToString();
            }
            activeCommand <- None
            stdoutOutputBuffer.Clear() |> ignore
            stderrOutputBuffer.Clear() |> ignore
            this.ProcessNextQueueElement()
        else
            stdoutOutputBuffer.Append newData |> ignore
        ()
    *)
    
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
                        stderrOutputBuffer.Append newChar |> ignore
                ()
        )

    member this.TaskReadStdout () : System.Threading.Tasks.Task =
        let promptPossible = ref true
        let currentLine = ref (new System.Text.StringBuilder())
        let checkIfActiveCommandFinished (character:char) (position:int) =
            let promptString = "nuXmv > "
            let updatePromptPossible ()=
                //position is 0-based
                if !promptPossible = false then
                    ()
                else
                    if position >= promptString.Length  then
                        promptPossible := false
                    else
                        let characterInPrompt = promptString.Chars(position)
                        if character <> characterInPrompt then
                            promptPossible := false
            updatePromptPossible ()
            let isPrompt : bool =
                !promptPossible && position = promptString.Length-1
            if isPrompt && activeCommand.IsSome then
                let newFinishedCommand = {
                    QueueCommandResult.Command = activeCommand.Value.Command;
                    QueueCommandResult.Stdout = stdoutOutputBuffer.ToString();
                    QueueCommandResult.Stderr = stderrOutputBuffer.ToString();
                }
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
                        currentLine.Value.Append newChar |> ignore
                        stdoutOutputBuffer.Append currentLine.Value |> ignore
                        currentLine.Value.Clear() |> ignore
                        promptPossible := true
                    else
                        currentLine.Value.Append newChar |> ignore
                        checkIfActiveCommandFinished newChar (currentLine.Value.Length - 1)
                ()
        )

    member this.TaskWaitForEnd () : System.Threading.Tasks.Task<bool> =
        System.Threading.Tasks.Task<bool>.Factory.StartNew(
            fun () ->
                proc.WaitForExit()
                true //<-- this Value gets interesting, when we define a timeout (see pattern)
        )
            
    member this.AppendQueueCommand (command:QueueCommand) =
        // NuXmv uses GNU readline and accepts commands from it. So it might be necessary to strip them out from the input-stream
        // TODO: check if in valid state (use expectedModeOfProgramAfterQueue)
        if NuXmvCommandHelpers.isCommandExecutableInMode command.Command expectedModeOfProgramAfterQueue <> true then
            failwith "Command not executable in mode after queue"
        commandQueueToProcess.Enqueue(command)
        
    member this.AppendQueueCommands (commands:QueueCommand list) =
        commands |> List.iter this.AppendQueueCommand

    member this.ExecuteCommand (command:ICommand) =
        let queueCommand = {
            QueueCommand.Command = command;
            QueueCommand.ActionsToExecuteAfterSuccess = [];
        }
        commandQueueToProcess.Enqueue(queueCommand)
        
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


    member this.StartNuXmvInteractive () : unit =
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

        //proc.EnableRaisingEvents <- true // process emits an exit event if killed or exits
        (*
        Old system:
        // be cautious: stdoutReceivedNewInput is only called, when the inputline is finished by a newline!!!!
        //              the command prompt does "nuXmv >" does not contain a line ending
        // From MSDN (Analogue for StandardError)
        //   Follow these steps to perform asynchronous read operations on StandardOutput for a Process :
        //   1. Set UseShellExecute to false.
        //   2. Set RedirectStandardOutput to true.
        //   3. Add your event handler to the OutputDataReceived event. The event handler must match the System.Diagnostics.DataReceivedEventHandler delegate signature.
        //   4. Start the Process.
        //   5. Call BeginOutputReadLine for the Process. This call starts asynchronous read operations on StandardOutput.
        proc.OutputDataReceived.Add (this.stdoutReceivedNewInput)
        proc.ErrorDataReceived.Add (this.stderrReceivedNewInput)
        proc.Start() |> ignore
        proc.BeginOutputReadLine ()
        proc.BeginErrorReadLine ()
        *)
        // New system (avoids the problem with the newline
        // Inspiration:
        //  - http://alabaxblog.info/2013/06/redirectstandardoutput-beginoutputreadline-pattern-broken/
        //  - https://gist.github.com/alabax/11353282

        processOutputReader <- this.TaskReadStdout ()
        processErrorReader <- this.TaskReadStderr ()
        processWaiter <- this.TaskWaitForEnd ()
        ()
                
    member this.ProcessNextQueueElement () =
        if activeCommand.IsSome then
            ()
        else
            if commandQueueToProcess.Count > 0 then
                let commandToExecute = commandQueueToProcess.Dequeue()
                activeCommand <- Some(commandToExecute)
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
            stringBuilder.AppendLine (commandToString.ExportICommand entry.Command) |> ignore
            stringBuilder.AppendLine entry.Stdout |> ignore
            stringBuilder.AppendLine entry.Stderr |> ignore
            stringBuilder.AppendLine "==========" |> ignore
        commandQueueResults |> Seq.iter printEntry
        stringBuilder.ToString()