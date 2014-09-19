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

type internal ExecutePrism() =
    

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
            System.Environment.SetEnvironmentVariable("PATH",System.Environment.GetEnvironmentVariable("PATH")+";"+prismLibDir);

        let fileNameToPrismDll = System.IO.Path.Combine(prismDir,"lib","prism.dll")
        let prismMachineCode = FileSystem.GetDllMachineType(fileNameToPrismDll)
        if javaMachineCode <> prismMachineCode then
           let failString = sprintf "java VM and prism version are not compiled for the same architecture. Please replace prism by a version compiled for java version of %s (%s)" javaExe (javaMachineCode.ToString())
           failwith failString
        prismDir

    static member argumentForJava (arguments:string) : string =
        let prismDir = ExecutePrism.FindPrismAndAddToPath ()
        let classpath =
            let stringFromBat = """%PRISM_DIR%\lib\prism.jar;%PRISM_DIR%\classes;%PRISM_DIR%;%PRISM_DIR%\lib\pepa.zip;%PRISM_DIR%\lib\*"""
            stringFromBat.Replace("%PRISM_DIR%",prismDir)
        sprintf """-Djava.library.path="%s\lib" -classpath "%s" prism.PrismCL %s""" prismDir classpath arguments

    static member IsPrismRunable () : bool =        
        let javaExe = ExecutePrism.FindJava ()
        use proc = new System.Diagnostics.Process()        
        proc.StartInfo.Arguments <- ExecutePrism.argumentForJava "-help"
        proc.StartInfo.FileName <- javaExe
        proc.StartInfo.WindowStyle <-  System.Diagnostics.ProcessWindowStyle.Hidden
        proc.StartInfo.CreateNoWindow <-  true
        proc.StartInfo.UseShellExecute <-  false
        //proc.StartInfo.RedirectStandardOutput <-  true
        //proc.StartInfo.RedirectStandardError <-  true
        proc.StartInfo.RedirectStandardInput <-  true
        //proc.StartInfo.WorkingDirectory
        proc.Start() |> ignore
        proc.StandardInput.AutoFlush <- true
        
        proc.WaitForExit ()
        
        // TODO lib needs to be added to PATH, otherwise prism can't find required dll-files
        // http://stackoverflow.com/questions/2998343/adding-a-directory-temporarily-to-windows-7s-dll-search-paths

        //let stderr = proc.StandardError.ReadToEnd()
        //let stdout = proc.StandardOutput.ReadToEnd()

        let exitCode = proc.ExitCode
        // under windows there are no negative values. Thus exit code -1 becomes 255 (2-complement)
        match exitCode with
            | 0 -> true
            | _ -> false

    (* 
    member this.TaskReadStderr () : System.Threading.Tasks.Task =
        System.Threading.Tasks.Task.Factory.StartNew(
            fun () -> 
                // http://msdn.microsoft.com/en-us/library/system.io.streamreader.readline(v=vs.110).aspx
                while proc.StandardError.EndOfStream <> true  do
                    let newLine = proc.StandardError.ReadLine()
                    if newLine.StartsWith commandEndingStringStderr then
                        stderrOutputBuffer.AppendLine newLine |> ignore  //remove, if marker should not appear in stderr
                        stderrFinishedBlocker.Set () |> ignore
                    else
                        stderrOutputBuffer.AppendLine newLine |> ignore
                stderrFinishedBlocker.Set () |> ignore
        )
                
    member this.TaskReadStdout () : System.Threading.Tasks.Task =
        let FinishCommandAndReleaseBlocker () =
            let newFinishedCommand = {
                NuXmvCommandResultBasic.Command = activeCommand.Value;
                NuXmvCommandResultBasic.Stdout = stdoutOutputBuffer.ToString();
                NuXmvCommandResultBasic.Stderr = stderrOutputBuffer.ToString();
                NuXmvCommandResultBasic.Failure = None; //Assume no failure occurred. If a failure occurred, ExecuteCommand detects it and corrects the result
            }
            lastCommandResult <-  Some(newFinishedCommand)
            activeCommand <- None
            stdoutOutputBuffer.Clear() |> ignore
            stderrOutputBuffer.Clear() |> ignore
            stdoutAndCommandFinishedBlocker.Set() |> ignore
        System.Threading.Tasks.Task.Factory.StartNew(
            fun () -> 
                let mutable needToRemovePromptFromCurrentLine = false //Before the first command is no prompt
                while proc.StandardOutput.EndOfStream <> true do
                    let newLine = proc.StandardOutput.ReadLine()
                    let newLineCleared =
                        // we need to clean out the prompt after a new command
                        // otherwise the check "newLine.StartsWith commandEndingStringStdout"
                        // is not true, when the prompt is before the marker
                        if needToRemovePromptFromCurrentLine && newLine.StartsWith(promptString) then
                            needToRemovePromptFromCurrentLine <- false
                            newLine.Remove(0,promptString.Length)
                        else
                            newLine
                    if newLineCleared.StartsWith commandEndingStringStdout then
                        stdoutOutputBuffer.AppendLine newLineCleared |> ignore //remove, if marker should not appear in stdout
                        stderrFinishedBlocker.WaitOne() |> ignore
                        FinishCommandAndReleaseBlocker ()
                        needToRemovePromptFromCurrentLine <- true
                        ()
                    else                        
                        stdoutOutputBuffer.AppendLine newLineCleared |> ignore
                // process definitively terminated here, because otherwise we wouldn't have received a EndOfStream-Token
                // we set the currentModeOfProgram here, because only here we can assure, that
                //    * we read everything from stderr
                //    * the main thread still waits in ExecuteCommand and there is no race-condition between the
                //      current command and a next command, which cannot be processed anymore, because nuXmv terminated.
                currentModeOfProgram<-NuXmvModeOfProgramm.Terminated //must occur before FinishCommandAndReleaseBlocker
                stderrFinishedBlocker.WaitOne() |> ignore
                FinishCommandAndReleaseBlocker ()
                ()
        )

    member this.TaskWaitForEnd (timeInMs:int) : System.Threading.Tasks.Task<bool> =
        System.Threading.Tasks.Task<bool>.Factory.StartNew(
            fun () ->
                if timeInMs > 0 then
                    let result = proc.WaitForExit(timeInMs)
                    result
                else
                    proc.WaitForExit()
                    true
        )*)