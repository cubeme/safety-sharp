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


type internal ExecuteSpin =

    val private filename : string
    // good to know: Prism only prints to stdout, even if errors occur. So only buffer for stdout necessary
    val stdoutOutputBuffer : System.Text.StringBuilder
    

    
    // pan may take a long time, so we use a waiter
    val mutable panOutputReader : System.Threading.Tasks.Task
    val mutable panWaiter : System.Threading.Tasks.Task    
    val panProc : System.Diagnostics.Process



    val panResults : System.Collections.Concurrent.BlockingCollection<string*bool> //(string contains the result. bool tells, if it was the last element

    new (filename : string) as this =
        {
            filename = filename;
            stdoutOutputBuffer = new System.Text.StringBuilder ();
            panOutputReader = null;
            panWaiter = null;
            panProc = new System.Diagnostics.Process();
            panResults = new System.Collections.Concurrent.BlockingCollection<string*bool>(); //by default blockingcollection uses a fifo-queue.
        }
        then
            //let spinResult = this.ExecuteSpin (filename)
            ExecuteSpin.AddCompilerToPath () 
            //let compilerResult = this.ExecuteCompiler ()
            //do this.ExecutePan ()


    ///////////////////////////////////////
    // FIND x (x \in Spin, Compiler)
    ///////////////////////////////////////

    
    static member FindSpin () : string =
        let tryCandidate (filename:string) : bool =
            System.IO.File.Exists filename

        let spinCandidatesManual = [
            "..\\..\\..\\..\\Dependencies\\spin627.exe";
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
    
    static member IsSpinRunnable () : bool =
        let spinExe = ExecuteSpin.FindSpin ()
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


    static member FindCompiler () : string =
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
    
    
    static member AddCompilerToPath () =
        let compiler = ExecuteSpin.FindCompiler ()        
        let compilerDir = 
            let directoryOfMingwBin = System.IO.Directory.GetParent compiler
            directoryOfMingwBin.Parent.FullName

        let dirsInPath = System.Environment.GetEnvironmentVariable("PATH").Split(';')
        if Array.exists (fun elem -> elem = compilerDir) dirsInPath then
            ()
        else
            // Add libdir to PATH
            // http://stackoverflow.com/questions/2998343/adding-a-directory-temporarily-to-windows-7s-dll-search-paths
            System.Environment.SetEnvironmentVariable("PATH",System.Environment.GetEnvironmentVariable("PATH")+";"+compilerDir);
        ()

        
    static member IsCompilerRunnable () : bool =
        let compilerExe = ExecuteSpin.FindCompiler ()
        use proc = new System.Diagnostics.Process()        
        do proc.StartInfo.Arguments <- "-V"
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
    
    (*

    member private this.ExecuteSpin (inputFile:string)  =
        let argumentForSpin (arguments:string) : string =
            sprintf """-a %s""" inputFile        
        let spin = ExecuteSpin.FindSpin ()

        this.proc.StartInfo.Arguments <- argumentForSpin inputFile
        this.proc.StartInfo.FileName <- spin
        this.proc.StartInfo.WindowStyle <-  System.Diagnostics.ProcessWindowStyle.Hidden
        this.proc.StartInfo.CreateNoWindow <-  true
        this.proc.StartInfo.UseShellExecute <-  false
        this.proc.StartInfo.RedirectStandardOutput <-  true
        this.proc.StartInfo.RedirectStandardError <-  false
        this.proc.StartInfo.RedirectStandardInput <-  true
        this.proc.Start() |> ignore
        this.proc.StandardInput.AutoFlush <- true        
        this.processOutputReader <- this.TaskReadStdout ()
        this.processWaiter <- this.TaskWaitForEnd (0)
        ()
    
    member private this.ExecuteCompiler ()  =
        let argumentForCompiler : string =
            "-o pan.exe pan.c"        
        let compiler = ExecuteSpin.FindCompiler ()
        this.proc.StartInfo.Arguments <- argumentForCompiler
        this.proc.StartInfo.FileName <- compiler
        this.proc.StartInfo.WindowStyle <-  System.Diagnostics.ProcessWindowStyle.Hidden
        this.proc.StartInfo.CreateNoWindow <-  true
        this.proc.StartInfo.UseShellExecute <-  false
        this.proc.StartInfo.RedirectStandardOutput <-  true
        this.proc.StartInfo.RedirectStandardError <-  false
        this.proc.StartInfo.RedirectStandardInput <-  true
        this.proc.Start() |> ignore
        this.proc.StandardInput.AutoFlush <- true        
        this.processOutputReader <- this.TaskReadStdout ()
        this.processWaiter <- this.TaskWaitForEnd (0)
        ()
    
    member private this.ExecutePan ()  =
        let argumentForPan : string =
            ""
        
        let compiler = ExecuteSpin.FindCompiler ()
        this.proc.StartInfo.Arguments <- argumentForPan
        this.proc.StartInfo.FileName <- compiler
        this.proc.StartInfo.WindowStyle <-  System.Diagnostics.ProcessWindowStyle.Hidden
        this.proc.StartInfo.CreateNoWindow <-  true
        this.proc.StartInfo.UseShellExecute <-  false
        this.proc.StartInfo.RedirectStandardOutput <-  true
        this.proc.StartInfo.RedirectStandardError <-  false
        this.proc.StartInfo.RedirectStandardInput <-  true
        this.proc.Start() |> ignore
        this.proc.StandardInput.AutoFlush <- true        
        this.processOutputReader <- this.TaskReadStdout ()
        this.processWaiter <- this.TaskWaitForEnd (0)
        ()
        
    member this.IsPanRunning () =
        let processes = [this.processOutputReader;this.processWaiter]
        processes |> List.forall (fun elem -> elem.Status = System.Threading.Tasks.TaskStatus.Running)
   
    
    member this.WaitUntilPrismTerminates () =
        System.Threading.Tasks.Task.WaitAll(this.processOutputReader,this.processWaiter)
        this.proc.ExitCode

    member this.GetNextResult () : string option =
        // TODO:
        //   - No concurrent access from different threads
        // Note if you change this function:
        //   - Changes might enable harmful sequences, which may lead to an inifinite blocking of GetNextResult() (race condition).
        //     Suppose GetNextResult gets called two times, but TaskReadStdout only adds one final element to an empty queue.
        //     Assure that the guard .IsCompleted() returns "true" the second time. This prevents the function to wait infinitely
        //     at the point ".Take()".
        if this.completeResults.IsCompleted then
            None
        else
            let (nextResult,wasLastElement) = this.completeResults.Take() //Blocks until new element arrives
            if wasLastElement then
                this.completeResults.CompleteAdding() //Do not allow adding. If 
            Some(nextResult)

    member this.GetAllResults () : string list =
        let rec collectAllResults acc =
            match this.GetNextResult () with
                | Some(entry) -> collectAllResults (entry::acc)
                | None -> acc
        collectAllResults [] |> List.rev
        
                        
    member private this.TaskReadStdout () : System.Threading.Tasks.Task =
        // TODO: see PrismExecute.fs for how to output partial results (for GUIs, etc...)
        
        let separator = "---------------------------------------------------------------------" // see file Spin/PrismLog.java/printSeparator()
        System.Threading.Tasks.Task.Factory.StartNew(
            fun () -> 
                while this.proc.StandardOutput.EndOfStream <> true  do
                    let newLine = this.proc.StandardOutput.ReadLine()
                    if newLine = separator then
                        let newEntry = this.stdoutOutputBuffer.ToString()
                        this.stdoutOutputBuffer.Clear() |> ignore
                        this.completeResults.Add((newEntry,false))
                    else
                        this.stdoutOutputBuffer.AppendLine newLine |> ignore
                let lastEntry = this.stdoutOutputBuffer.ToString()
                this.stdoutOutputBuffer.Clear() |> ignore
                this.completeResults.Add((lastEntry,true))
        )

    member private this.TaskWaitForEnd (timeInMs:int) : System.Threading.Tasks.Task<bool> =
        System.Threading.Tasks.Task<bool>.Factory.StartNew(
            fun () ->
                if timeInMs > 0 then
                    let result = this.proc.WaitForExit(timeInMs)
                    result
                else
                    this.proc.WaitForExit()
                    true
        )
        *)