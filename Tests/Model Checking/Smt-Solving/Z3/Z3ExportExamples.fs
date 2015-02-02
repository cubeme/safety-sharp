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

namespace Z3AstToFile.Tests

open System
open NUnit.Framework

open TestHelpers
open AstTestHelpers

open SafetySharp.Analysis.SmtSolving.SmtLib2.Ast
open SafetySharp.Analysis.SmtSolving.SmtLib2.Parser
open SafetySharp.Analysis.SmtSolving.SmtLib2.Parser.SmtLib2ParsingResult
open SafetySharp.Analysis.SmtSolving.SmtLib2.SMTLIB2Convenience
open SafetySharp.Analysis.SmtSolving.Z3.Ast
open SafetySharp.Analysis.SmtSolving.Z3.Parser
open SafetySharp.Analysis.SmtSolving.Z3.AstToString
open SafetySharp.Analysis.SmtSolving.Z3.Execute

open Z3ExamplesFiles

type Z3ExportExampleTests() =
    
    let exporter = ExportZ3AstToFile()
    let exampleFileSimplify1bString = exporter.Export exampleFileSimplify1bAst

    
    [<Test>]
    member this.``Z3 is executed correctly``() =
        // /h shows help, without any parameter z3 fails
        let z3ExecutionResult = ExecuteZ3Script.ExecuteZ3Script "/h"
        z3ExecutionResult.HasSucceeded =? true
(*                      
    [<Test>]
    member this.``Output file is available after being written``() =
        let filename = "simplify1b.z3"
        use disposer = FSharpUncategorisedHelpers.FileHelpers.createCustomTemporaryFile filename exampleFileSimplify1bString true
        let result = System.IO.File.Exists filename 
        //disposer.Delete ()
        result =? true

    [<Test>]
    member this.``Output file is parsed correctly by Z3``() =
        let filename = "simplify1b.z3"
        use disposer = FSharpUncategorisedHelpers.FileHelpers.createCustomTemporaryFile filename exampleFileSimplify1bString false
        let z3ExecutionResult = ExecuteZ3Script.ExecuteZ3Script ("/smt2 " + filename)
        let hassucceded = match z3ExecutionResult with
                            | Z3ExecuteExternal.Z3Result.Failed (outbuffer,errorbuffer) -> failwith (outbuffer + errorbuffer)
                            | Z3ExecuteExternal.Z3Result.Successful (outbuffer,errorbuffer) -> true
        //disposer.Delete ()
        hassucceded  =? true
               
    [<Test>]
    member this.``Output file is not parsed correctly, when a valid example returns "unsupported"``() =
        false  =? true
        //TODO: Test for unsupported feature!!!! THIS HAS TO BE INCLUDED IN TEST ``Output file is parsed correctly by Z3``, too.
    *)