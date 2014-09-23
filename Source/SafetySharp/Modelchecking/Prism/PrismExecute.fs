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

namespace SafetySharp.Internal.Modelchecking.Prism

open SafetySharp.Internal.Utilities

type internal ExecutePrism =
    val private arguments : string
    // good to know: Prism only prints to stdout, even if errors occur. So only buffer for stdout necessary
    val stdoutOutputBuffer : System.Text.StringBuilder
    
    val mutable processOutputReader : System.Threading.Tasks.Task
    val mutable processWaiter : System.Threading.Tasks.Task

    val proc : System.Diagnostics.Process

    val completeResults : System.Collections.Concurrent.BlockingCollection<string*bool> //(string contains the result. bool tells, if it was the last element

    new (arguments : string) as this =
        {
            arguments = arguments;
            stdoutOutputBuffer = new System.Text.StringBuilder ();
            processOutputReader = null;
            processWaiter = null;
            proc = new System.Diagnostics.Process();
            completeResults = new System.Collections.Concurrent.BlockingCollection<string*bool>(); //by default blockingcollection uses a fifo-queue.
        }
        then
            this.ExecutePrismWithArgument()


    static member FindJava () : string =
        let tryCandidate (filename:string) : bool =
            System.IO.File.Exists filename
        let javaCandidate =
            "C:\\ProgramData\\Oracle\\Java\\javapath\\java.exe"
        if tryCandidate javaCandidate <> true then
            failwith "Java not found"
        javaCandidate

    static member FindPrismDir () : string =
        //TODO: What to do on Linux?!?
        //      Gets executed several times. Calculate in constructor and remove the static?!?
        //      Or is it better to define stuff like this in the GUI and create a PATH-Manager class and call
        //      here just something like 'getSafetySharpEnvironmentVariable("PRISM")' or both (automatic guess
        //      for command-line and custom in GUI)?!?
        let tryCandidate (filename:string) : bool =
            System.IO.File.Exists filename

        let prismCandidatesManual = [
            "..\\..\\..\\..\\Dependencies\\prism\\bin\\prism.bat";
        ]
        let prismCandidatesInPath =
            let paths=System.Environment.GetEnvironmentVariable("PATH").Split(';')
            paths |> Array.map (fun path -> System.IO.Path.Combine(path,"bin","prism.bat"))
                  |> Array.toList
        let prismCandidateOfNuXmvDir =
            let path=System.Environment.GetEnvironmentVariable("PRISM_DIR")
            if path = null then
                []
            else
                [System.IO.Path.Combine(path,"bin","prism.bat")]
        
        let candidates = prismCandidatesManual @ prismCandidatesInPath @ prismCandidateOfNuXmvDir
        let fileNameToPrismBat =
            match candidates |> Seq.tryFind tryCandidate with
                | Some(filename) -> filename
                | None -> failwith "Please add path to prism.bat into PATH\n or set the environmental variable PRISM_DIR to the prism top level directory \n or copy prism into the dependency directory . You can download prism from http://www.prismmodelchecker.org/"
                
        let prismDir = 
            let directoryOfPrismBat = System.IO.Directory.GetParent fileNameToPrismBat
            directoryOfPrismBat.Parent.FullName
        prismDir
    
    
    static member FindPrismAndAddToPath (): string =
        // TODO:
        //   - check for correct java (minimal version and vendor)
        ExecutePrism.EnsurePrismArchitectureSameAsJavaArchitecture ()
        ExecutePrism.AddPrismLibToPath()
        let prismDir = ExecutePrism.FindPrismDir ()
        prismDir
       
        
    static member AddPrismLibToPath () =
        let prismDir = ExecutePrism.FindPrismDir ()
        let prismLibDir = System.IO.Path.Combine(prismDir,"lib")
        let dirsInPath = System.Environment.GetEnvironmentVariable("PATH").Split(';')
        if Array.exists (fun elem -> elem = prismLibDir) dirsInPath then
            ()
        else
            // Add libdir to PATH
            // http://stackoverflow.com/questions/2998343/adding-a-directory-temporarily-to-windows-7s-dll-search-paths
            System.Environment.SetEnvironmentVariable("PATH",System.Environment.GetEnvironmentVariable("PATH")+";"+prismLibDir);
        ()

    static member EnsurePrismArchitectureSameAsJavaArchitecture () =
        let javaExe = ExecutePrism.FindJava ()
        let prismDir = ExecutePrism.FindPrismDir ()
        let javaMachineCode = FileSystem.GetDllMachineType(javaExe)
        let fileNameToPrismDll = System.IO.Path.Combine(prismDir,"lib","prism.dll")
        let prismMachineCode = FileSystem.GetDllMachineType(fileNameToPrismDll)        
        if javaMachineCode <> prismMachineCode then
           let failString = sprintf "java VM and prism version are not compiled for the same architecture. Please replace prism by a version compiled for java version of %s (%s)" javaExe (javaMachineCode.ToString())
           failwith failString
           
            
    member private this.ExecutePrismWithArgument ()  =
        let argumentForJava (arguments:string) : string =
            let prismDir = ExecutePrism.FindPrismAndAddToPath ()
            let classpath =
                let stringFromBat = """%PRISM_DIR%\lib\prism.jar;%PRISM_DIR%\classes;%PRISM_DIR%;%PRISM_DIR%\lib\pepa.zip;%PRISM_DIR%\lib\*"""
                stringFromBat.Replace("%PRISM_DIR%",prismDir)
            sprintf """-Djava.library.path="%s\lib" -classpath "%s" prism.PrismCL %s""" prismDir classpath arguments            
        let javaExe = ExecutePrism.FindJava ()
        this.proc.StartInfo.Arguments <- argumentForJava this.arguments
        this.proc.StartInfo.FileName <- javaExe
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
        

    static member IsPrismRunable () : bool =
        let executePrism = ExecutePrism("-help")
        let exitCode = executePrism.WaitUntilPrismTerminates ()
        // under windows there are no negative values. Thus exit code -1 becomes 255 (2-complement)
        match exitCode with
            | 0 -> true
            | _ -> false

    member this.IsPrismRunning () =
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
                        
    member private this.TaskReadStdout () : System.Threading.Tasks.Task =
        let separator = "---------------------------------------------------------------------" // see file prism/PrismLog.java/printSeparator()
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