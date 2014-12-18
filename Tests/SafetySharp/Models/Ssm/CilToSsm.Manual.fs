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

        let ssm = 
            methodDef 
            |> Cil.getMethodBody 
            |> CilToSsm.transform

        SsmToCSharp.transform ssm |> printfn "%s"
        ssm

    [<Test>]
    let ``ternary operator before return`` () =
        transform "int M(int x) { var y = x > 0 ? -1 : 1; return y - 1; }" =? 
            let varName = "__tmp_6_0"
            let condition = BExpr (VarExpr (Arg "x"), Gt, IntExpr 0)
            let thenStm = AsgnStm (Local varName, IntExpr -1)
            let elseStm = AsgnStm (Local varName, IntExpr 1)
            let ifStm = IfStm (condition, thenStm, Some elseStm)
            let retStm = RetStm <| Some (BExpr (VarExpr (Local varName), Sub, IntExpr 1))
            SeqStm [ifStm; retStm]

    [<Test>]
    let ``short-circuit 'or' for Boolean variables and return`` () = 
        transform "int M(bool x, bool y) { if (x || y) return -1; return 0; }" =? 
            let condition = UExpr (Not, BExpr (VarExpr (Arg "x"), Or, VarExpr (Arg "y")))
            let thenStm = RetStm (Some (IntExpr 0))
            let elseStm = RetStm (Some (IntExpr -1))
            IfStm (condition, thenStm, Some elseStm)

    [<Test>]
    let ``short-circuit 'and' for Boolean variables and return`` () = 
        transform "int M(bool x, bool y) { if (x && y) return -1; return 0; }" =? 
            let condition = UExpr (Not, BExpr (VarExpr (Arg "x"), And, VarExpr (Arg "y")))
            let thenStm = RetStm (Some (IntExpr 0))
            let elseStm = RetStm (Some (IntExpr -1))
            IfStm (condition, thenStm, Some elseStm)

    [<Test>]
    let ``tenary operator with preincrement side effect`` () =
        transform "void M(int x, int y, int z) { z = x > 0 ? ++y : 0; }" =? 
            let condition = BExpr (VarExpr (Arg "x"), Gt, IntExpr 0)
            let thenStm = 
                let assignStm1 = AsgnStm (Local "__tmp_9_0", VarExpr (Arg "y"))
                let assignStm2 = AsgnStm (Local "__tmp_10_0", BExpr (VarExpr (Local "__tmp_9_0"), Add, IntExpr 1))
                let assignStm3 = AsgnStm (Arg "y", BExpr (VarExpr (Arg "y"), Add, IntExpr 1))
                SeqStm [assignStm1; assignStm2; assignStm3]
            let elseStm = AsgnStm (Local "__tmp_10_0", IntExpr 0)
            let ifStm = IfStm (condition, thenStm, Some elseStm)
            let assignStm = AsgnStm (Arg "z", VarExpr (Local "__tmp_10_0"))
            SeqStm [ifStm; assignStm; RetStm None]

    [<Test>]
    let ``tenary operator with postdecrement side effect`` () =
        transform "void M(int x, int y, int z) { z = x > 0 ? y-- : 0; }" =? 
            let condition = BExpr (VarExpr (Arg "x"), Gt, IntExpr 0)
            let thenStm = 
                let assignStm1 = AsgnStm (Local "__tmp_9_0", VarExpr (Arg "y"))
                let assignStm2 = AsgnStm (Local "__tmp_10_0", VarExpr (Local "__tmp_9_0"))
                let assignStm3 = AsgnStm (Arg "y", BExpr (VarExpr (Arg "y"), Sub, IntExpr 1))
                SeqStm [assignStm1; assignStm2; assignStm3]
            let elseStm = AsgnStm (Local "__tmp_10_0", IntExpr 0)
            let ifStm = IfStm (condition, thenStm, Some elseStm)
            let assignStm = AsgnStm (Arg "z", VarExpr (Local "__tmp_10_0"))
            SeqStm [ifStm; assignStm; RetStm None]

    [<Test>]
    let ``nested ternary operator`` () =
        transform "int M(bool b, bool c) { var x = 1 + (b ? (c ? 4 : 2) : 3); return x; }" =? 
            SeqStm [
                AsgnStm (Local "__tmp_5_0", IntExpr 1)
                IfStm (
                    VarExpr (Arg "b"),
                    SeqStm [
                        AsgnStm (Local "__tmp_9_0", VarExpr (Local "__tmp_5_0"))
                        IfStm (
                            VarExpr (Arg "c"),
                            SeqStm [
                                AsgnStm (Local "__tmp_10_0", IntExpr 4)
                                AsgnStm (Local "__tmp_10_1", VarExpr (Local "__tmp_9_0"))
                            ],
                            SeqStm [
                                AsgnStm (Local "__tmp_10_0", IntExpr 2)
                                AsgnStm (Local "__tmp_10_1", VarExpr (Local "__tmp_5_0"))
                            ] |> Some
                        )
                    ],
                    SeqStm [
                        AsgnStm (Local "__tmp_10_0", IntExpr 3)
                        AsgnStm (Local "__tmp_10_1", IntExpr 1)
                    ] |> Some
                )
                RetStm (Some (BExpr (VarExpr (Local "__tmp_10_1"), Add, VarExpr (Local "__tmp_10_0"))))
            ]