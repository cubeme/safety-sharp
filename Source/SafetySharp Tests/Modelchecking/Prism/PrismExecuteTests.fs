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

namespace SafetySharp.Tests.Modelchecking.Prism.PrismExecuteTests


open NUnit.Framework
open SafetySharp.Tests
open SafetySharp.Tests.Modelchecking
open SafetySharp.Internal.Utilities
open SafetySharp.Internal.Modelchecking
open SafetySharp.Internal.Modelchecking.Prism



[<TestFixture>]
module PrismExecuteTestsBasic =

    [<Test>]
    let ``Prism is in PATH or in dependency folder`` () =
        let path = ExecutePrism.FindPrismAndAddToPath ()
        (path.Length > 0) =? true
        
    [<Test>]
    let ``Prism is runable and shows help`` () =
        ExecutePrism.IsPrismRunable() =? true

    [<Test>]
    let ``Prism executes the dice-test`` () =
        let prismDir = ExecutePrism.FindPrismDir ()
        let exampleDir = System.IO.Path.Combine(prismDir,"examples","dice")
        let exampleModel = System.IO.Path.Combine(exampleDir,"dice.pm")
        let exampleProperties = System.IO.Path.Combine(exampleDir,"dice.pctl")
        let exampleFlags = "-const x=1:2:5" //from 1 to 5 with step 2 => 1,3,5 will be checked
        let maximalVerbosityAndOutput = "-v -extraddinfo -extrareachinfo  -exportmodel stdout.all"
        let commandLine = sprintf "%s %s %s %s" exampleModel exampleProperties maximalVerbosityAndOutput exampleFlags 
        let executePrism = ExecutePrism(commandLine)
        let result = executePrism.GetNextResult()
        ()

        
    [<Test>]
    let ``Prism missing constant`` () =
        let prismDir = ExecutePrism.FindPrismDir ()
        let exampleDir = System.IO.Path.Combine(prismDir,"examples","dice")
        let exampleModel = System.IO.Path.Combine(exampleDir,"dice.pm")
        let exampleProperties = System.IO.Path.Combine(exampleDir,"dice.pctl")
        let maximalVerbosityAndOutput = "-v -extraddinfo -extrareachinfo"
        let commandLine = sprintf "%s %s %s" exampleModel exampleProperties maximalVerbosityAndOutput
        let executePrism = ExecutePrism(commandLine)
        let result = executePrism.GetNextResult()
        ()


    // TODO: Catch errors like "Error: Undefined constant "x" must be defined."
    // Command line arguments in "prism/PrismCL.java/parseArguments"
    // -const a=1,b=5.6,c=true