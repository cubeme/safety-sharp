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

namespace SafetySharp.Analysis.Modelchecking.Boogie

type internal ExecuteBoogie =
    

    val private filename : string
    // to check: is interesting output on stderr
    val boogieResults : System.Collections.Concurrent.BlockingCollection<string*bool> //(string contains the result. bool tells, if it was the last element

    val mutable private boogieTask : System.Threading.Tasks.Task<bool>
    // for partial results

    new (filename : string) as this =
        {
            filename = filename;
            boogieResults = new System.Collections.Concurrent.BlockingCollection<string*bool>(); //by default blockingcollection uses a fifo-queue.
            boogieTask = null;
        }
        then
            do this.boogieTask <- this.ExecuteBoogieAsync


    ///////////////////////////////////////
    // FIND x (x \in Boogie, Boogie-Z3)
    ///////////////////////////////////////

    
    static member FindBoogie : string =
        let tryCandidate (filename:string) : bool =
            System.IO.File.Exists filename

        let boogieCandidatesManual = [
            "..\\..\\Dependencies\\Boogie\\Boogie.exe";
        ]
        let boogieCandidanteOfBoogieDir =
            let path=System.Environment.GetEnvironmentVariable("BOOGIE_DIR")
            if path = null then
                []
            else
                [System.IO.Path.Combine(path,"Boogie.exe")]
        
        let candidates = boogieCandidatesManual @ boogieCandidanteOfBoogieDir
        let fileNameToBoogieExe =
            match candidates |> Seq.tryFind tryCandidate with
                | Some(filename) -> filename
                | None -> failwith "Please set the environmental variable BOOGIE_DIR to the Boogie top level directory \n or copy Boogie into the sub directory 'Boogie' of the dependency directory. You can download Boogie from http://boogie.codeplex.com/"
        fileNameToBoogieExe
    
    static member IsBoogieRunnable : bool =
        let boogieExe = ExecuteBoogie.FindBoogie
        use proc = new System.Diagnostics.Process()        
        do proc.StartInfo.Arguments <- "Boogie ../../Examples/Boogie/example1Structured.bpl" //boogie needs an input file, otherwise it returns an error
        do proc.StartInfo.FileName <- boogieExe
        do proc.StartInfo.WindowStyle <-  System.Diagnostics.ProcessWindowStyle.Hidden
        do proc.StartInfo.CreateNoWindow <-  true
        do proc.StartInfo.UseShellExecute <-  false
        do proc.StartInfo.RedirectStandardOutput <-  true
        do proc.Start() |> ignore
        do proc.WaitForExit ()
        let exitCode = proc.ExitCode
        match exitCode with
            | 0 ->
                let output = proc.StandardOutput.ReadToEnd()
                if output.StartsWith "Boogie program verifier version 2.2.30705.1126" then
                    failwith "You should use a newer version of boogie. Try to compile the source code repository"
                    false
                else
                    true
            | _ ->
                false

    static member FindZ3 : string =
        let tryCandidate (filename:string) : bool =
            System.IO.File.Exists filename

        let z3CandidatesManual = [
            "..\\..\\Dependencies\\Boogie\\z3.exe";
        ]
        let z3CandidateOfBoogieDir =
            let path=System.Environment.GetEnvironmentVariable("BOOGIE_DIR")
            if path = null then
                []
            else
                [System.IO.Path.Combine(path,"bin","gcc.exe")]
        
        let candidates = z3CandidatesManual @ z3CandidateOfBoogieDir
        let fileNameToZ3exe =
            match candidates |> Seq.tryFind tryCandidate with
                | Some(filename) -> filename
                | None -> failwith "Please copy a binary of z3.exe into the directory of Boogie. This directory is either the directory of the environmental variable BOOGIE_DIR or the Boogie top level directory \n or the sub directory 'Boogie' of the dependency directory. You can download Z3 from http://z3.codeplex.com/"
        fileNameToZ3exe
    
    
        
    static member IsZ3Runnable : bool =
        let z3Exe = ExecuteBoogie.FindZ3
        use proc = new System.Diagnostics.Process()        
        do proc.StartInfo.Arguments <- "/?"
        do proc.StartInfo.FileName <- z3Exe
        do proc.StartInfo.WindowStyle <-  System.Diagnostics.ProcessWindowStyle.Hidden
        do proc.StartInfo.CreateNoWindow <-  true
        do proc.StartInfo.UseShellExecute <-  false
        do proc.StartInfo.RedirectStandardOutput <-  true
        do proc.Start() |> ignore
        do proc.WaitForExit ()
        let exitCode = proc.ExitCode
        match exitCode with
            | 0 ->
                //let output = proc.StandardOutput.ReadToEnd()
                true
            | _ ->
                false
        
    ///////////////////////////////////////
    // Execute Boogie
    ///////////////////////////////////////         
    
    //returns true, if successful
    member private this.ExecuteBoogieAsync : System.Threading.Tasks.Task<bool> =
        let tcs = new System.Threading.Tasks.TaskCompletionSource<bool>();
        let argumentForBoogie : string =
            sprintf """%s""" this.filename
        let boogieExe = ExecuteBoogie.FindBoogie
        let proc = new System.Diagnostics.Process()
        proc.StartInfo.Arguments <- argumentForBoogie
        proc.StartInfo.FileName <- boogieExe
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
                        do this.boogieResults.Add((newLine,isLastEntry))
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
            
    member this.IsVerificationRunning =
        this.boogieTask.Status = System.Threading.Tasks.TaskStatus.Running
   
    member this.WaitUntilVerificationTerminates =
        this.boogieTask.Wait()

    member this.GetNextBoogieResult () : string option =
        // TODO:
        //   - No concurrent access from different threads
        // Note if you change this function:
        //   - Changes might enable harmful sequences, which may lead to an infinite blocking of GetNextPanResult() (race condition).
        //     Suppose GetNextPanResult gets called two times, but TaskReadStdout only adds one final element to an empty queue.
        //     Assure that the guard .IsCompleted() returns "true" the second time. This prevents the function to wait infinitely
        //     at the point ".Take()".
        if this.boogieResults.IsCompleted then
            None
        else
            let (nextResult,wasLastElement) = this.boogieResults.Take() //Blocks until new element arrives
            if wasLastElement then
                this.boogieResults.CompleteAdding() //Do not allow adding. If 
            Some(nextResult)

    member this.GetAllResults () : string list =
        let rec collectAllResults acc =
            match this.GetNextBoogieResult () with
                | Some(entry) -> collectAllResults (entry::acc)
                | None -> acc
        collectAllResults [] |> List.rev
        
    member this.WasSuccessful : bool =
        this.boogieTask.Result


open SafetySharp.Workflow
     
type internal ExecuteBoogie with
    
    static member runBoogie : SimpleWorkflowFunction<SafetySharp.FileSystem.FileName,string,unit> = workflow {
        let! file = getState ()
        let (SafetySharp.FileSystem.FileName(filename)) = file
        let executeBoogie = new ExecuteBoogie(filename)
        let result = executeBoogie.GetAllResults() |> String.concat "\n"
        do! updateState result
    }

