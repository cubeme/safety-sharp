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


    static member FindPrism (): string =
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
        let fileNameToPrismDll = System.IO.Path.Combine(prismDir,"lib","prism.dll")
        let prismMachineCode = FileSystem.GetDllMachineType(fileNameToPrismDll)
        if javaMachineCode <> prismMachineCode then
           let failString = sprintf "java VM and prism version are not compiled for the same architecture. Please replace prism by a version compiled for java version of %s (%s)" javaExe (javaMachineCode.ToString())
           failwith failString
        prismDir

    static member argumentForJava (arguments:string) : string =
        let prismDir = ExecutePrism.FindPrism ()
        let classpath =
            let stringFromBat = """%PRISM_DIR%\lib\prism.jar;%PRISM_DIR%\classes;%PRISM_DIR%;%PRISM_DIR%\lib\pepa.zip;%PRISM_DIR%\lib\*"""
            stringFromBat.Replace("%PRISM_DIR",prismDir)
        sprintf """-Djava.library.path="%s\lib" -classpath "%s" prism.PrismCL %s""" prismDir classpath arguments

    static member IsPrismRunable () : bool =        
        let javaExe = ExecutePrism.FindJava ()
        use proc = new System.Diagnostics.Process()        
        proc.StartInfo.Arguments <- ExecutePrism.argumentForJava "-help"
        proc.StartInfo.FileName <- javaExe
        proc.StartInfo.WindowStyle <-  System.Diagnostics.ProcessWindowStyle.Hidden
        proc.StartInfo.CreateNoWindow <-  true
        proc.StartInfo.UseShellExecute <-  false
        proc.StartInfo.RedirectStandardOutput <-  false
        proc.StartInfo.RedirectStandardError <-  false
        proc.StartInfo.RedirectStandardInput <-  false
        proc.Start() |> ignore        
        proc.WaitForExit()
        let exitCode = proc.ExitCode
        // under windows there are no negative values. Thus exit code -1 becomes 255 (2-complement)
        match exitCode with
            | 0 -> true
            | 255 -> false
            | 2 -> true //help
            | _ -> false