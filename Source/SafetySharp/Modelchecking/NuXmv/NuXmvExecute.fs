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


open System.Diagnostics

type internal NuXmvResult =
    | Successful of string * string
    | Failed of string * string
    with
        member this.HasSucceeded with get () =
                                    match this with
                                        | Successful (_,_) -> true
                                        | Failed (_,_) -> false

type internal ExecuteNuXmv() =
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

    static member ExecuteNuXmv (arguments:string) : NuXmvResult =
        let stdoutOutputBuffer = new System.Text.StringBuilder ()
        let stderrOutputBuffer = new System.Text.StringBuilder ()
        use proc = new Process()
        
        proc.StartInfo.Arguments <- arguments
        proc.StartInfo.FileName <- ExecuteNuXmv.FindNuXmv ()
        proc.StartInfo.WindowStyle <-  ProcessWindowStyle.Hidden
        proc.StartInfo.CreateNoWindow <-  true
        proc.StartInfo.UseShellExecute <-  false
        proc.StartInfo.RedirectStandardOutput <-  true
        proc.StartInfo.RedirectStandardError <-  true
        proc.StartInfo.RedirectStandardInput <-  true

        //proc.EnableRaisingEvents = true |> ignore
        proc.ErrorDataReceived.Add (fun dataReceivedEvArgs -> (stderrOutputBuffer.Append(dataReceivedEvArgs.Data) |> ignore) )
        proc.OutputDataReceived .Add (fun dataReceivedEvArgs -> (stdoutOutputBuffer.Append(dataReceivedEvArgs.Data) |> ignore))

        proc.Start() |> ignore
        
        proc.BeginErrorReadLine ()
        proc.BeginOutputReadLine ()

        // proc.StandardInput.WriteLine("input for nuXmv");
        // proc.StandardInput.Flush();
        
        proc.WaitForExit()
        
        let exitCode = proc.ExitCode
        match exitCode with
            | 0 -> Successful(stdoutOutputBuffer.ToString(), stderrOutputBuffer.ToString())
            | _ -> Failed(stdoutOutputBuffer.ToString(), stderrOutputBuffer.ToString())
