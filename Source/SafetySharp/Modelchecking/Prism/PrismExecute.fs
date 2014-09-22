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
    val stdoutOutputBuffer : System.Text.StringBuilder
    val stderrOutputBuffer : System.Text.StringBuilder
    
    val mutable processOutputReader : System.Threading.Tasks.Task
    val mutable processErrorReader : System.Threading.Tasks.Task
    val mutable processWaiter : System.Threading.Tasks.Task

    val proc : System.Diagnostics.Process

    new (arguments : string) as this =
        {
            arguments = arguments;
            stdoutOutputBuffer = new System.Text.StringBuilder ();
            stderrOutputBuffer = new System.Text.StringBuilder ();
            processOutputReader = null;
            processErrorReader = null;
            processWaiter = null;
            proc = new System.Diagnostics.Process()
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


    static member FindPrismAndAddToPath (): string =
        // TODO:
        //   - check for correct java (minimal version and vendor)
        //   - for windows and for linux and mac???
        let tryCandidate (filename:string) : bool =
            System.IO.File.Exists filename
        
        let javaExe = ExecutePrism.FindJava ()

        let javaMachineCode = FileSystem.GetDllMachineType(javaExe)
                
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
        
        let prismLibDir = System.IO.Path.Combine(prismDir,"lib")
        
        if List.exists (fun elem -> elem = prismLibDir) prismCandidatesInPath then
            ()
        else
            // Add libdir to PATH
            // http://stackoverflow.com/questions/2998343/adding-a-directory-temporarily-to-windows-7s-dll-search-paths
            System.Environment.SetEnvironmentVariable("PATH",System.Environment.GetEnvironmentVariable("PATH")+";"+prismLibDir);

        let fileNameToPrismDll = System.IO.Path.Combine(prismDir,"lib","prism.dll")
        let prismMachineCode = FileSystem.GetDllMachineType(fileNameToPrismDll)
        if javaMachineCode <> prismMachineCode then
           let failString = sprintf "java VM and prism version are not compiled for the same architecture. Please replace prism by a version compiled for java version of %s (%s)" javaExe (javaMachineCode.ToString())
           failwith failString
        prismDir
            
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
        this.proc.StartInfo.RedirectStandardError <-  true
        this.proc.StartInfo.RedirectStandardInput <-  true
        this.proc.Start() |> ignore
        this.proc.StandardInput.AutoFlush <- true
        this.processOutputReader <- this.TaskReadStdout ()
        this.processErrorReader <- this.TaskReadStderr ()
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
        false
    
    
    member this.WaitUntilPrismTerminates () =
        System.Threading.Tasks.Task.WaitAll(this.processOutputReader,this.processErrorReader,this.processWaiter)
        this.proc.ExitCode

    member this.GetNextResult () =
        ()

    member private this.TaskReadStderr () : System.Threading.Tasks.Task =
        System.Threading.Tasks.Task.Factory.StartNew(
            fun () -> 
                while this.proc.StandardError.EndOfStream <> true  do
                    let newLine = this.proc.StandardError.ReadLine()
                    this.stderrOutputBuffer.AppendLine newLine |> ignore
        )
                
    member private this.TaskReadStdout () : System.Threading.Tasks.Task =
        System.Threading.Tasks.Task.Factory.StartNew(
            fun () -> 
                while this.proc.StandardOutput.EndOfStream <> true  do
                    let newLine = this.proc.StandardOutput.ReadLine()
                    this.stdoutOutputBuffer.AppendLine newLine |> ignore
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