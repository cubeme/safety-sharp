﻿// The MIT License (MIT)
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

namespace SafetySharp.ExternalTools.PromelaSpin


open NUnit.Framework
open SafetySharp
open SafetySharp.Analysis.Modelchecking
open SafetySharp.Analysis.Modelchecking.PromelaSpin



[<TestFixture>]
module PromelaExecuteTestsBasic =

    [<Test>]
    let ``Spin is in PATH or in dependency folder`` () =
        let path = ExecuteSpin.FindSpin
        (path.Length > 0) =? true
        
    [<Test>]
    let ``Spin is runable and shows help`` () =
        ExecuteSpin.IsSpinRunnable =? true

    [<Test>]
    let ``Compiler is in PATH or in dependency folder`` () =
        let path = ExecuteSpin.FindCompiler
        (path.Length > 0) =? true
        
    [<Test>]
    let ``Compiler is runable and shows help`` () =
        ExecuteSpin.IsCompilerRunnable =? true

    [<Test>]
    let ``Spin verifies the samSmokeTest1.pm file`` () =
        let inputFile = SafetySharp.FileSystem.FileName("""../../Examples/Promela/samSmokeTest1.pml""")
        let executePromelaSpin = ExecuteSpin(inputFile)
        let results = executePromelaSpin.GetAllResults ()
        executePromelaSpin.WasSuccessful =? true
        ()
