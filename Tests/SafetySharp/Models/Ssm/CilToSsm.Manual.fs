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

namespace Ssm

open System.Linq
open NUnit.Framework
open Mono.Cecil
open SafetySharp.Models
open SafetySharp.Models.Ssm

[<TestFixture>]
module CilToSsmManual =
    let private transform csharpCode = 
        let t = "TestType"
        let csharpCode = sprintf "class %s { %s }" t csharpCode
        let compilation = TestCompilation csharpCode
        let assembly = compilation.GetAssemblyDefinition ()
        let typeDef = assembly.MainModule.GetType t
        let methodDef = typeDef.Methods.Single (fun m' -> m'.Name = "M")

        methodDef 
        |> Cil.getMethodBody 
        |> CilToSsm.transform

    [<Test; Ignore("Failing")>]
    let ``simple control flow`` () =
        let varName = "__tmp_6_0"
        let condition = BExpr (VarExpr (Arg "x"), Gt, IntExpr 0)
        let thenStm = AsgnStm (Local varName, IntExpr -1)
        let elseStm = AsgnStm (Local varName, IntExpr 1)
        let ifStm = IfStm (condition, thenStm, Some elseStm)
        let assignStm = AsgnStm (Local "y", VarExpr (Local varName))
        let retStm = RetStm <| Some (BExpr (VarExpr (Local "y"), Sub, IntExpr 1))
        transform "int M(int x) { var y = x > 0 ? -1 : 1; return y - 1; }" =?
            
            SeqStm (ifStm, SeqStm (assignStm, retStm))
