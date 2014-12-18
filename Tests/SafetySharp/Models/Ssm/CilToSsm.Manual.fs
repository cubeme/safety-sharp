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
module ``CilToSsm (manual tests)`` =
    let private transform csharpCode = 
        let t = "TestType"
        let csharpCode = sprintf "class %s { %s }" t csharpCode
        let compilation = TestCompilation csharpCode
        let assembly = compilation.GetAssemblyDefinition ()
        let typeDef = assembly.MainModule.GetType t
        let methodDef = typeDef.Methods.Single (fun m' -> m'.Name = "M")
        let m = CilToSsm.transformMethod methodDef

        SsmToCSharp.transform m |> printfn "%s"
        m

    let private arg name t = Arg (name, t)
    let private local name t = Local (name, t)
    let private tmp = CilToSsm.freshLocal

    [<Test>]
    let ``ternary operator before return`` () =
        transform "int M(int x) { var y = x > 0 ? -1 : 1; return y - 1; }" =? 
            let tmp = tmp 6 0 IntType
            let condition = BExpr (VarExpr (arg "x" IntType), Gt, IntExpr 0)
            let thenStm = AsgnStm (tmp, IntExpr -1)
            let elseStm = AsgnStm (tmp, IntExpr 1)
            let ifStm = IfStm (condition, thenStm, Some elseStm)
            let retStm = RetStm <| Some (BExpr (VarExpr tmp, Sub, IntExpr 1))
            { 
                Name = "M" 
                Params = [ { Var = Arg ("x", IntType); InOut = false } ]
                Body = SeqStm [ifStm; retStm]
                Return = Some IntType
                Locals = [tmp]
            }

    [<Test>]
    let ``short-circuit 'or' for Boolean variables and return`` () = 
        transform "int M(bool x, bool y) { if (x || y) return -1; return 0; }" =? 
            let condition = UExpr (Not, BExpr (VarExpr (arg "x" BoolType), Or, VarExpr (arg "y" BoolType)))
            let thenStm = RetStm (Some (IntExpr 0))
            let elseStm = RetStm (Some (IntExpr -1))
            { 
                Name = "M" 
                Params = [ { Var = Arg ("x", BoolType); InOut = false }; { Var = Arg ("y", BoolType); InOut = false } ]
                Body = IfStm (condition, thenStm, Some elseStm)
                Return = Some IntType
                Locals = []
            }

    [<Test>]
    let ``short-circuit 'and' for Boolean variables and return`` () = 
        transform "int M(bool x, bool y) { if (x && y) return -1; return 0; }" =? 
            let condition = UExpr (Not, BExpr (VarExpr (arg "x" BoolType), And, VarExpr (arg "y" BoolType)))
            let thenStm = RetStm (Some (IntExpr 0))
            let elseStm = RetStm (Some (IntExpr -1))
            { 
                Name = "M" 
                Params = [ { Var = Arg ("x", BoolType); InOut = false }; { Var = Arg ("y", BoolType); InOut = false } ]
                Body = IfStm (condition, thenStm, Some elseStm)
                Return = Some IntType
                Locals = []
            }

    [<Test>]
    let ``tenary operator with preincrement side effect`` () =
        transform "void M(int x, int y, int z) { z = x > 0 ? ++y : 0; }" =? 
            let condition = BExpr (VarExpr (arg "x" IntType), Gt, IntExpr 0)
            let thenStm = 
                let assignStm1 = AsgnStm (tmp 9 0 IntType, VarExpr (arg "y" IntType))
                let assignStm2 = AsgnStm (tmp 10 0 IntType, BExpr (VarExpr (tmp 9 0 IntType), Add, IntExpr 1))
                let assignStm3 = AsgnStm (arg "y" IntType, BExpr (VarExpr (arg "y" IntType), Add, IntExpr 1))
                SeqStm [assignStm1; assignStm2; assignStm3]
            let elseStm = AsgnStm (tmp 10 0 IntType, IntExpr 0)
            let ifStm = IfStm (condition, thenStm, Some elseStm)
            let assignStm = AsgnStm (arg "z" IntType, VarExpr (tmp 10 0 IntType))
            { 
                Name = "M" 
                Params = 
                    [ 
                        { Var = Arg ("x", IntType); InOut = false }
                        { Var = Arg ("y", IntType); InOut = false } 
                        { Var = Arg ("z", IntType); InOut = false } 
                    ]
                Body = SeqStm [ifStm; assignStm; RetStm None]
                Return = None
                Locals = [ tmp 9 0 IntType; tmp 10 0 IntType ]
            }

    [<Test>]
    let ``tenary operator with postdecrement side effect`` () =
        transform "void M(int x, int y, int z) { z = x > 0 ? y-- : 0; }" =? 
            let condition = BExpr (VarExpr (arg "x" IntType), Gt, IntExpr 0)
            let thenStm = 
                let assignStm1 = AsgnStm (tmp 9 0 IntType, VarExpr (arg "y" IntType))
                let assignStm2 = AsgnStm (tmp 10 0 IntType, VarExpr (tmp 9 0 IntType))
                let assignStm3 = AsgnStm (arg "y" IntType, BExpr (VarExpr (arg "y" IntType), Sub, IntExpr 1))
                SeqStm [assignStm1; assignStm2; assignStm3]
            let elseStm = AsgnStm (tmp 10 0 IntType, IntExpr 0)
            let ifStm = IfStm (condition, thenStm, Some elseStm)
            let assignStm = AsgnStm (arg "z" IntType, VarExpr (tmp 10 0 IntType))
            { 
                Name = "M" 
                Params = 
                    [ 
                        { Var = Arg ("x", IntType); InOut = false }
                        { Var = Arg ("y", IntType); InOut = false } 
                        { Var = Arg ("z", IntType); InOut = false } 
                    ]
                Body = SeqStm [ifStm; assignStm; RetStm None]
                Return = None
                Locals = [ tmp 9 0 IntType; tmp 10 0 IntType ]
            }

    [<Test>]
    let ``nested ternary operator`` () =
        transform "int M(bool b, bool c) { var x = 1 + (b ? (c ? 4 : 2) : 3); return x; }" =? 
            { 
                Name = "M" 
                Params = [ { Var = Arg ("b", BoolType); InOut = false }; { Var = Arg ("c", BoolType); InOut = false } ]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 5 0 IntType, IntExpr 1)
                        IfStm (
                            VarExpr (arg "b" BoolType),
                            SeqStm [
                                AsgnStm (tmp 9 0 IntType, VarExpr (tmp 5 0 IntType))
                                IfStm (
                                    VarExpr (arg "c" BoolType),
                                    SeqStm [
                                        AsgnStm (tmp 10 0 IntType, IntExpr 4)
                                        AsgnStm (tmp 10 1 IntType, VarExpr (tmp 9 0 IntType))
                                    ],
                                    SeqStm [
                                        AsgnStm (tmp 10 0 IntType, IntExpr 2)
                                        AsgnStm (tmp 10 1 IntType, VarExpr (tmp 5 0 IntType))
                                    ] |> Some
                                )
                            ],
                            SeqStm [
                                AsgnStm (tmp 10 0 IntType, IntExpr 3)
                                AsgnStm (tmp 10 1 IntType, IntExpr 1)
                            ] |> Some
                        )
                        RetStm (Some (BExpr (VarExpr (tmp 10 1 IntType), Add, VarExpr (tmp 10 0 IntType))))
                    ]
                Return = Some IntType
                Locals = [ tmp 5 0 IntType; tmp 9 0 IntType; tmp 10 0 IntType; tmp 10 1 IntType ]
            }