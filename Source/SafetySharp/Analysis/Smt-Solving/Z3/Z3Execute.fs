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

namespace SafetySharp.Internal.SmtSolving.Z3.Execute

open System.Diagnostics
open SafetySharp.Internal.SmtSolving.SmtLib2.Ast
open SafetySharp.Internal.SmtSolving.SmtLib2.Parser
open SafetySharp.Internal.SmtSolving.Z3.Ast

open FParsec

exception NotImplementedYetException

type internal Z3Result =
    | Successful of string * string
    | Failed of string * string
     with
       member this.HasSucceeded
           with get () =
               match this with
                   | Successful (_,_) -> true
                   | Failed (_,_) -> false

// TODO: - Möglichkeit schaffen einer Environment-Variable, die den Pfad enthält
//       - FindPath-Funktion, die versucht den Ort geschickt zu erraten

// http://msdn.microsoft.com/en-us/library/system.diagnostics.process.start.aspx
// http://msdn.microsoft.com/en-us/library/system.diagnostics.process.aspx
// http://msdn.microsoft.com/en-us/library/system.diagnostics.process.startinfo.aspx

// http://stackoverflow.com/questions/415620/redirect-console-output-to-textbox-in-separate-program-c-sharp
// http://stackoverflow.com/questions/353601/capturing-nslookup-shell-output-with-c-sharp

type internal ExecuteZ3Script() = 
    static member ExecuteZ3Script (arguments:string) : Z3Result =
        let stdoutOutputBuffer = new System.Text.StringBuilder ()
        let stderrOutputBuffer = new System.Text.StringBuilder ()
        use proc = new Process()
        
        proc.StartInfo.Arguments <- arguments
        proc.StartInfo.FileName <- "..\\..\\..\\..\\Dependencies\\z3.exe"
        proc.StartInfo.WindowStyle <-  ProcessWindowStyle.Normal
        proc.StartInfo.CreateNoWindow <-  true
        proc.StartInfo.UseShellExecute <-  false
        proc.StartInfo.RedirectStandardOutput <-  true
        proc.StartInfo.RedirectStandardError <-  true
        proc.StartInfo.RedirectStandardInput <-  true

        //proc.EnableRaisingEvents = true |> ignore
        // TODO: hier könnte man noch zu den Buffern einen TimeCode oder sowas hinzufügen
        proc.ErrorDataReceived.Add (fun dataReceivedEvArgs -> (stderrOutputBuffer.Append(dataReceivedEvArgs.Data) |> ignore) )
        proc.OutputDataReceived .Add (fun dataReceivedEvArgs -> (stdoutOutputBuffer.Append(dataReceivedEvArgs.Data) |> ignore))

        proc.Start() |> ignore
        
        proc.BeginErrorReadLine ()
        proc.BeginOutputReadLine ()

        // proc.StandardInput.WriteLine("hier Eingabe für das Programm");
        // proc.StandardInput.Flush();
        
        proc.WaitForExit()

        //let (output:string) = proc.StandardOutput.ReadToEnd() <--- braucht man wohl nicht mehr mit den asynchronen Funktionen, die später vllt. nützlich werden können

        let exitCode = proc.ExitCode
        match exitCode with
            | 0 -> Successful(stdoutOutputBuffer.ToString(), stderrOutputBuffer.ToString())
            | _ -> Failed(stdoutOutputBuffer.ToString(), stderrOutputBuffer.ToString())


type internal Z3InteractiveState =
    | Z3StateOff
    | Z3ShuttingDown
    | Z3StateIdle
    | Z3StateCalculating

type internal ExecuteZ3Interactive() =
    let state : Z3InteractiveState ref = ref Z3StateOff
    let mutable proc : Process = null
    let stdoutOutputBuffer = new System.Text.StringBuilder ()
    let stderrOutputBuffer = new System.Text.StringBuilder ()
    let smt2common = new SMTCommonParser ()
        
    let ShutdownIntern  = (fun () -> System.Threading.Monitor.Enter state
                                     if !state <> Z3StateOff && !state <> Z3ShuttingDown then
                                        try
                                            state := Z3ShuttingDown
                                            proc.StandardInput.WriteLine("(exit)");
                                            proc.StandardInput.Flush();
                                            proc.WaitForExit()
                                            proc.Dispose ()
                                            proc <- null
                                            state := Z3InteractiveState.Z3StateOff
                                        with
                                          _ -> ()
                                     System.Threading.Monitor.Exit state
                          )


    member this.State 
        with get () = state


    member this.Start () =
        System.Threading.Monitor.Enter state
        if !state = Z3StateOff then
            proc <- new Process ()
        
            proc.StartInfo.Arguments <- "/smt2 /in"
            proc.StartInfo.FileName <- "..\\..\\..\\..\\Dependencies\\z3.exe"
            proc.StartInfo.WindowStyle <-  ProcessWindowStyle.Normal
            proc.StartInfo.CreateNoWindow <-  true
            proc.StartInfo.UseShellExecute <-  false
            proc.StartInfo.RedirectStandardOutput <-  true
            proc.StartInfo.RedirectStandardError <-  true
            proc.StartInfo.RedirectStandardInput <-  true
            //proc.EnableRaisingEvents <- true
            //proc.ErrorDataReceived.Add (fun dataReceivedEvArgs -> (stderrOutputBuffer.Append(dataReceivedEvArgs.Data) |> ignore) )
            //proc.OutputDataReceived.Add (fun dataReceivedEvArgs -> (stdoutOutputBuffer.Append(dataReceivedEvArgs.Data) |> ignore
            //                                                       )
            //                            )

            proc.Start() |> ignore        
            //proc.BeginErrorReadLine ()
            //proc.BeginOutputReadLine ()
            state := Z3StateIdle
        System.Threading.Monitor.Exit state
        

    member this.ExecuteCustomCommandAsync (input:string) : string =
        raise NotImplementedYetException
        
    member this.ExecuteCommandAsync (cmd:ICommand) : string =
        raise NotImplementedYetException

    member this.ExecuteCustomScriptAsync (cmds:string list) : string =
        raise NotImplementedYetException
                
    member this.ExecuteScriptAsync (cmds:ICommand list) : string =
        raise NotImplementedYetException


    (*
      Der FParsec-StreamReader liest, bis der Buffer voll ist oder er das Ende erreicht. Also nicht, bis er erfolgreich parsen kann. Dies führt dazu, dass
      wir selber das Ende finden müssen...

      Also: Ende des Outputs eines Befehls wird gefunden:

      Um auf das Ergebnis zuzugreifen, wäre es cool, eine Funktion zu haben, die ein Ergebnis liefert, und solange blockt, bis dieses vorhanden ist.
      Dies können wir folgendermaßen realisieren:
      - Einfach: Readline-Methode, die solange Readline macht und konkateniert, bis das Ende erreicht ist (laut unserer Hilfefunktion)
      - Kompliziert: Per Event wird in einen Buffer kopiert. Dieser Buffer wird mit einfach ausgewertet. Es gibt eine Taskqueue (let elementInQueue = new System.Threading.Tasks.TaskCompletionSource<string>())
                     Sobald Ende erreicht, wird ein Task in eine Queue eingehängt, der das Ergebnis als String enthält (task_outputdatareceived.SetResult string)
                     Zum Abrufen gibt es eine Funktion, diese nimmt den ersten Task aus der queue und macht auf diesen "Async.AwaitTask firstinQueue.Task |> result"        
    *)



    member this.ExecuteCustomCommand (input:string) : SExpr =
        let readCompleteSExpr strmreader : string =
            let seprtokenizer = new SMTSExpressionTokenizer()
            let mutable completed = false
            while completed <> true do
                let output = proc.StandardOutput.ReadLine () + "\n"
                completed <- (seprtokenizer.ParseNewInput output)
            seprtokenizer.StringProccessed
        proc.StandardInput.WriteLine input
        proc.StandardInput.Flush ()
        
        let sexprstr = readCompleteSExpr proc.StandardOutput
        match run smt2common.parseSExpr sexprstr with
            | Success(result, _, _)   -> result
            | Failure(errorMsg, _, _) -> failwith errorMsg
        

    member this.ExecuteCommand (cmd:ICommand) : string =
        raise NotImplementedYetException


    member this.ExecuteCustomScript (cmds:string list) : string =
        raise NotImplementedYetException
        
    member this.ExecuteScript (cmds:ICommand list) : string =
        raise NotImplementedYetException

             
    member x.Shutdown = ShutdownIntern
    override x.Finalize() = 
        ShutdownIntern ()
    interface System.IDisposable with
        member x.Dispose() =
            ShutdownIntern ()