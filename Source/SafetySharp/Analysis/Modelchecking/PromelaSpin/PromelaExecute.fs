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

namespace SafetySharp.Analysis.Modelchecking.PromelaSpin

(*
[<RequireQualifiedAccessAttribute>]
type PromelaSpinVerificationState =
    | NotStarted
    | Spin
    | Compiler
    | Pan
    | Completed 
*)

type internal ExecutePromelaSpin =
    

    val private filename : string
    // good to know: Prism only prints to stdout, even if errors occur. So only buffer for stdout necessary
    val mutable private spinStdoutOutput : string
    val mutable private compilerStdoutOutput : string
    val panResults : System.Collections.Concurrent.BlockingCollection<string*bool> //(string contains the result. bool tells, if it was the last element


    val mutable private completeVerificationTask : System.Threading.Tasks.Task<bool>
    // for partial results

    new (filename : string) as this =
        {
            filename = filename;
            spinStdoutOutput = "";
            compilerStdoutOutput = "";
            panResults = new System.Collections.Concurrent.BlockingCollection<string*bool>(); //by default blockingcollection uses a fifo-queue.
            completeVerificationTask = null;
        }
        then
            do ExecutePromelaSpin.AddCompilerToPath
            do this.completeVerificationTask <- this.ExecuteCompleteVerificationAsync


    ///////////////////////////////////////
    // FIND x (x \in Spin, Compiler)
    ///////////////////////////////////////

    
    static member FindSpin : string =
        let tryCandidate (filename:string) : bool =
            System.IO.File.Exists filename

        let spinCandidatesManual = [
            "..\\..\\Dependencies\\spin627.exe";
        ]
        let spinCandidatesInPath =
            let paths=System.Environment.GetEnvironmentVariable("PATH").Split(';')
            paths |> Array.map (fun path -> System.IO.Path.Combine(path,"spin627.exe"))
                  |> Array.toList
        let spinCandidanteOfSpinDir =
            let path=System.Environment.GetEnvironmentVariable("SPIN_DIR")
            if path = null then
                []
            else
                [System.IO.Path.Combine(path,"spin627.exe")]
        
        let candidates = spinCandidatesManual @ spinCandidatesInPath @ spinCandidanteOfSpinDir
        let fileNameToSpinExe =
            match candidates |> Seq.tryFind tryCandidate with
                | Some(filename) -> filename
                | None -> failwith "Please add path to spin627.exe into PATH\n or set the environmental variable SPIN_DIR to the Spin top level directory \n or copy Spin into the dependency directory. You can download Spin from http://www.http://spinroot.com/"
        fileNameToSpinExe
    
    static member IsSpinRunnable : bool =
        let spinExe = ExecutePromelaSpin.FindSpin
        use proc = new System.Diagnostics.Process()        
        do proc.StartInfo.Arguments <- "-V"
        do proc.StartInfo.FileName <- spinExe
        do proc.StartInfo.WindowStyle <-  System.Diagnostics.ProcessWindowStyle.Hidden
        do proc.StartInfo.CreateNoWindow <-  true
        do proc.StartInfo.UseShellExecute <-  false
        do proc.Start() |> ignore
        do proc.WaitForExit ()
        let exitCode = proc.ExitCode
        match exitCode with
            | 0 -> true
            | _ -> false


    static member FindCompiler : string =
        let tryCandidate (filename:string) : bool =
            System.IO.File.Exists filename

        let mingwCandidatesManual = [
            "D:\\MinGW\\bin\\gcc.exe";
            "C:\\MinGW\\bin\\gcc.exe";
        ]
        let mingwCandidatesInPath =
            let paths=System.Environment.GetEnvironmentVariable("PATH").Split(';')
            paths |> Array.map (fun path -> System.IO.Path.Combine(path,"gcc.exe"))
                  |> Array.toList
        let mingwCandidateOfNuXmvDir =
            let path=System.Environment.GetEnvironmentVariable("MINGW_DIR")
            if path = null then
                []
            else
                [System.IO.Path.Combine(path,"bin","gcc.exe")]
        
        let candidates = mingwCandidatesManual @ mingwCandidatesInPath @ mingwCandidateOfNuXmvDir
        let fileNameToMingwGcc =
            match candidates |> Seq.tryFind tryCandidate with
                | Some(filename) -> filename
                | None -> failwith "Please add path to gcc into PATH\n or set the environmental variable MINGW_DIR to the mingw top level directory \n. You can download mingw from http://www.mingw.org/"
        fileNameToMingwGcc
    
    
    static member AddCompilerToPath : unit =
        let compiler = ExecutePromelaSpin.FindCompiler        
        let compilerDir = 
            let directoryOfMingwBin = System.IO.Directory.GetParent compiler
            directoryOfMingwBin.FullName

        let dirsInPath = System.Environment.GetEnvironmentVariable("PATH").Split(';')
        if Array.exists (fun elem -> elem = compilerDir) dirsInPath then
            ()
        else
            // Add libdir to PATH
            // http://stackoverflow.com/questions/2998343/adding-a-directory-temporarily-to-windows-7s-dll-search-paths
            System.Environment.SetEnvironmentVariable("PATH",System.Environment.GetEnvironmentVariable("PATH")+";"+compilerDir);
        ()

        
    static member IsCompilerRunnable : bool =
        let compilerExe = ExecutePromelaSpin.FindCompiler
        use proc = new System.Diagnostics.Process()        
        do proc.StartInfo.Arguments <- "--help"
        do proc.StartInfo.FileName <- compilerExe
        do proc.StartInfo.WindowStyle <-  System.Diagnostics.ProcessWindowStyle.Hidden
        do proc.StartInfo.CreateNoWindow <-  true
        do proc.StartInfo.UseShellExecute <-  false
        do proc.Start() |> ignore
        do proc.WaitForExit ()
        let exitCode = proc.ExitCode
        match exitCode with
            | 0 -> true
            | _ -> false
        
    ///////////////////////////////////////
    // Execute x (x \in Spin, Compiler, Pan)
    ///////////////////////////////////////         
    
    member private this.ExecuteSpinAsync : System.Threading.Tasks.Task<bool> =
        let tcs = new System.Threading.Tasks.TaskCompletionSource<bool>();
        let argumentForSpin : string =
            sprintf """-a %s""" this.filename
        let spinExe = ExecutePromelaSpin.FindSpin        
        let proc = new System.Diagnostics.Process()        
        proc.StartInfo.Arguments <- argumentForSpin
        proc.StartInfo.FileName <- spinExe
        proc.StartInfo.WindowStyle <-  System.Diagnostics.ProcessWindowStyle.Hidden
        proc.StartInfo.CreateNoWindow <-  true
        proc.StartInfo.UseShellExecute <-  false
        proc.StartInfo.RedirectStandardOutput <-  true
        proc.StartInfo.RedirectStandardError <-  false
        proc.StartInfo.RedirectStandardInput <-  true  
        proc.EnableRaisingEvents <-  true
        let afterFinished () =        
            let exitCode = proc.ExitCode
            this.spinStdoutOutput <- proc.StandardOutput.ReadToEnd()
            match exitCode with
                | 0 -> tcs.SetResult(true)
                | _ -> tcs.SetResult(false)            
            proc.Dispose()
        do proc.Exited.Add ( fun _ -> afterFinished() )
        do proc.Start() |> ignore
        proc.StandardInput.AutoFlush <- true
        tcs.Task
                    
    //returns true, if successful
    member private this.ExecuteCompilerAsync : System.Threading.Tasks.Task<bool> =    
        let tcs = new System.Threading.Tasks.TaskCompletionSource<bool>();        
        let argumentForCompiler : string =
            "-o pan.exe pan.c"        
        let compiler = ExecutePromelaSpin.FindCompiler    
        let proc = new System.Diagnostics.Process()        
        proc.StartInfo.Arguments <- argumentForCompiler
        proc.StartInfo.FileName <- compiler
        proc.StartInfo.WindowStyle <-  System.Diagnostics.ProcessWindowStyle.Hidden
        proc.StartInfo.CreateNoWindow <-  true
        proc.StartInfo.UseShellExecute <-  false
        proc.StartInfo.RedirectStandardOutput <-  true
        proc.StartInfo.RedirectStandardError <-  false
        proc.StartInfo.RedirectStandardInput <-  true        
        proc.EnableRaisingEvents <-  true
        let afterFinished () =        
            let exitCode = proc.ExitCode
            this.compilerStdoutOutput <- proc.StandardOutput.ReadToEnd()
            match exitCode with
                | 0 -> tcs.SetResult(true)
                | _ -> tcs.SetResult(false)            
            proc.Dispose()
        do proc.Exited.Add ( fun _ -> afterFinished() )
        do proc.Start() |> ignore
        proc.StandardInput.AutoFlush <- true
        tcs.Task
            
    //returns true, if successful
    member private this.ExecutePanAsync : System.Threading.Tasks.Task<bool> =
        let tcs = new System.Threading.Tasks.TaskCompletionSource<bool>();
        let argumentForPan : string =
            "-m2000"        
        let panExe = "pan.exe"     
        let proc = new System.Diagnostics.Process()
        proc.StartInfo.Arguments <- argumentForPan
        proc.StartInfo.FileName <- panExe
        proc.StartInfo.WindowStyle <-  System.Diagnostics.ProcessWindowStyle.Hidden
        proc.StartInfo.CreateNoWindow <-  true
        proc.StartInfo.UseShellExecute <-  false
        proc.StartInfo.RedirectStandardOutput <-  true
        proc.StartInfo.RedirectStandardError <-  false
        proc.StartInfo.RedirectStandardInput <-  true      
        proc.EnableRaisingEvents <-  true  
        let startReadingOutput = new System.Threading.ManualResetEventSlim(false);
        let outputReaderTask : System.Threading.Tasks.Task =            
            System.Threading.Tasks.Task.Factory.StartNew(
                fun () ->
                    // before proc.StandardOutput could be read, the process must have been started
                    // TODO: see PrismExecute.fs for how to output partial results (for GUIs, etc...)
                    startReadingOutput.Wait()
                    while proc.StandardOutput.EndOfStream <> true do
                        let newLine = proc.StandardOutput.ReadLine()
                        let isLastEntry = proc.StandardOutput.EndOfStream
                        do this.panResults.Add((newLine,isLastEntry))
                        ()
                    
            )
        let afterFinished () =        
            let exitCode = proc.ExitCode //program exited
            outputReaderTask.Wait() //finished reading the output
            // outputReaderTask.Dispose() tasks should not be disposed.
            match exitCode with
                | 0 -> tcs.SetResult(true)
                | _ -> tcs.SetResult(false)            
            proc.Dispose() // now we can safely dispose the process. processes should be disposed
        do proc.Exited.Add ( fun _ -> afterFinished() )
        do proc.Start() |> ignore
        do startReadingOutput.Set() // proc.StandardOutput can only be accessed after proc.Start() 
        //if proc.Failed
        //  do this.panResults.Add(("pan could not be started",true))
        proc.StandardInput.AutoFlush <- true
        tcs.Task
            
    member private this.ExecuteCompleteVerificationAsync : System.Threading.Tasks.Task<bool> =
        let asyncTask = 
            async {
                let! spinSuccessful = Async.AwaitTask this.ExecuteSpinAsync
                if spinSuccessful = false then
                    do this.panResults.Add(("spin could not be started",true))
                    return false
                else
                    let! compilerSuccessful = Async.AwaitTask this.ExecuteCompilerAsync
                    if compilerSuccessful = false then
                        do this.panResults.Add(("compiler could not be started",true))
                        return false
                    else
                        let! panSuccessful = Async.AwaitTask this.ExecutePanAsync
                        if panSuccessful = false then
                            do this.panResults.Add(("pan could not be started",true))
                            return false
                        else
                            return true
            }
        Async.StartAsTask<bool> asyncTask

    member this.IsVerificationRunning =
        this.completeVerificationTask.Status = System.Threading.Tasks.TaskStatus.Running
   
    member this.WaitUntilVerificationTerminates =
        this.completeVerificationTask.Wait()

    member this.GetNextPanResult () : string option =
        // TODO:
        //   - No concurrent access from different threads
        // Note if you change this function:
        //   - Changes might enable harmful sequences, which may lead to an infinite blocking of GetNextPanResult() (race condition).
        //     Suppose GetNextPanResult gets called two times, but TaskReadStdout only adds one final element to an empty queue.
        //     Assure that the guard .IsCompleted() returns "true" the second time. This prevents the function to wait infinitely
        //     at the point ".Take()".
        if this.panResults.IsCompleted then
            None
        else
            let (nextResult,wasLastElement) = this.panResults.Take() //Blocks until new element arrives
            if wasLastElement then
                this.panResults.CompleteAdding() //Do not allow adding. If 
            Some(nextResult)

    member this.GetAllResults () : string list =
        let rec collectAllResults acc =
            match this.GetNextPanResult () with
                | Some(entry) -> collectAllResults (entry::acc)
                | None -> acc
        collectAllResults [] |> List.rev
        
    member this.WasSuccessful : bool =
        this.completeVerificationTask.Result