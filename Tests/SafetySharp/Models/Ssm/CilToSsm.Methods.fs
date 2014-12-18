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
module ``CilToSsm Method Transformations`` =
    let private transform csharpCode = 
        let t = "TestType"
        let csharpCode = sprintf "class %s { %s }" t csharpCode
        let compilation = TestCompilation csharpCode
        let assembly = compilation.GetAssemblyDefinition ()
        let typeDef = assembly.MainModule.GetType t
        let methodDef = typeDef.Methods.Single (fun m' -> m'.Name = "M")

        printfn "MSIL of method body:"
        methodDef.Body.Instructions |> Seq.iteri (printfn "%3i: %A")

        printfn ""
        printfn "Transformed method:"
        let m = CilToSsm.transformMethod methodDef
        SsmToCSharp.transform m |> printfn "%s"
        m

    let private arg name t = Arg (name, t)
    let private local name t = Local (name, t)
    let private tmp = CilToSsm.freshLocal

    [<Test>]
    let ``read from ref parameter`` () =
        transform "int M(ref int x) { return x; }" =?
            {
                Name = "M"
                Return = Some IntType
                Params = [ { Var = arg "x" IntType; InOut = true } ]
                Locals = []
                Body = RetStm (Some (VarExpr (arg "x" IntType)))
            }

    [<Test>]
    let ``write to ref parameter`` () =
        transform "void M(ref int x) { x = 17; }" =?
            {
                Name = "M"
                Return = None
                Params = [ { Var = arg "x" IntType; InOut = true } ]
                Locals = []
                Body = SeqStm [AsgnStm (arg "x" IntType, IntExpr 17); RetStm None]
            }

    [<Test>]
    let ``method with in, inout, and out parameters`` () =
        transform "double M(double x, ref bool y, out int z) { z = y ? 1 : 0; return 3.0; }" =?
            {
                Name = "M"
                Return = Some DoubleType
                Params = 
                    [ 
                        { Var = arg "x" DoubleType; InOut = false }
                        { Var = arg "y" BoolType; InOut = true } 
                        { Var = arg "z" IntType; InOut = true } 
                    ]
                Locals = [tmp 7 0 IntType]
                Body =
                    SeqStm [
                        IfStm (
                            VarExpr (arg "y" BoolType),
                            AsgnStm (tmp 7 0 IntType, IntExpr 1),
                            AsgnStm (tmp 7 0 IntType, IntExpr 0) |> Some
                        )
                        AsgnStm (arg "z" IntType, VarExpr (tmp 7 0 IntType))
                        RetStm (Some (DoubleExpr 3.0))
                    ]
            }

    [<Test>]
    let ``method with complex side effects`` () =
        transform "void M(int z) { z *= z-- * --z; }" =?
            {
                Name = "M"
                Return = None
                Params = [ { Var = arg "z" IntType; InOut = false } ]
                Locals = [tmp 5 0 IntType; tmp 10 0 IntType]
                Body =
                    SeqStm [
                        AsgnStm (tmp 5 0 IntType, VarExpr (arg "z" IntType))
                        AsgnStm (arg "z" IntType, BExpr (VarExpr (arg "z" IntType), Sub, IntExpr 1))
                        AsgnStm (tmp 10 0 IntType, VarExpr (arg "z" IntType))
                        AsgnStm (arg "z" IntType, BExpr (VarExpr (arg "z" IntType), Sub, IntExpr 1))
                        AsgnStm (arg "z" IntType, 
                            BExpr (VarExpr (tmp 5 0 IntType), Mul, 
                                BExpr (VarExpr (tmp 5 0 IntType), Mul, BExpr (VarExpr (tmp 10 0 IntType), Sub, IntExpr 1))))
                        RetStm None
                    ]
            }

    [<Test>]
    let ``method with complex side effects when parameter is byref`` () =
        transform "void M(ref int z) { z *= z-- * --z; }" =?
            let local = local "__loc_0" IntType
            {
                Name = "M"
                Return = None
                Params = [ { Var = arg "z" IntType; InOut = true } ]
                Locals = [local; tmp 10 0 IntType; tmp 17 0 IntType; tmp 19 0 IntType]
                Body =
                    SeqStm [
                        AsgnStm (local, VarExpr (arg "z" IntType))
                        AsgnStm (tmp 10 0 IntType, VarExpr (arg "z" IntType))
                        AsgnStm (arg "z" IntType, BExpr (VarExpr local, Sub, IntExpr 1))
                        AsgnStm (tmp 17 0 IntType, VarExpr local)
                        AsgnStm (local, BExpr (VarExpr (arg "z" IntType), Sub, IntExpr 1))
                        AsgnStm (tmp 19 0 IntType, VarExpr (arg "z" IntType))
                        AsgnStm (arg "z" IntType, VarExpr local)
                        AsgnStm (arg "z" IntType, 
                            BExpr (VarExpr (tmp 10 0 IntType), Mul, 
                                BExpr (VarExpr (tmp 17 0 IntType), Mul, VarExpr local)))
                        RetStm None
                    ]
            }

    [<Test>]
    let ``method with in and inout parameters, side effects, and complex control flow`` () =
        transform "void M(ref bool y, ref int z) { z = y ? z++ : ((y = !y) ? z-- : --z); }" =?
            let local0 = local "__loc_0" BoolType
            let local1 = local "__loc_1" IntType
            let argY = arg "y" BoolType
            let argZ = arg "z" IntType
            {
                Name = "M"
                Return = None
                Params = [ { Var = arg "y" BoolType; InOut = true }; { Var = arg "z" IntType; InOut = true } ]
                Locals = [local1; tmp 41 0 IntType; tmp 43 0 IntType; local0; tmp 31 0 IntType; tmp 21 0 IntType]
                Body =
                    SeqStm [
                        IfStm (
                            VarExpr argY,
                            SeqStm [
                                AsgnStm (local1, VarExpr argZ)
                                AsgnStm (tmp 41 0 IntType, VarExpr argZ)
                                AsgnStm (argZ, BExpr (VarExpr local1, Add, IntExpr 1))
                                AsgnStm (tmp 43 0 IntType, VarExpr local1)
                            ],
                            SeqStm [
                                   AsgnStm (local0, BExpr (VarExpr argY, Eq, BoolExpr false))
                                   AsgnStm (argY, BExpr (VarExpr argY, Eq, BoolExpr false))
                                   IfStm (
                                       VarExpr (local0),
                                       SeqStm [
                                           AsgnStm (local1, VarExpr argZ)
                                           AsgnStm (tmp 31 0 IntType, VarExpr argZ)
                                           AsgnStm (argZ, BExpr (VarExpr local1, Sub, IntExpr 1))
                                           AsgnStm (tmp 43 0 IntType, VarExpr local1)
                                       ],
                                       SeqStm [
                                           AsgnStm (local1, BExpr (VarExpr argZ, Sub, IntExpr 1))
                                           AsgnStm (tmp 21 0 IntType, VarExpr argZ)
                                           AsgnStm (argZ, VarExpr local1)
                                           AsgnStm (tmp 43 0 IntType, VarExpr local1)
                                       ] |> Some
                                   )
                            ] |> Some
                        )
                        AsgnStm (argZ, VarExpr (tmp 43 0 IntType))
                        RetStm None
                    ]
            }

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
                Params = [ { Var = arg "x" IntType; InOut = false } ]
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
                Params = [ { Var = arg "x" BoolType; InOut = false }; { Var = arg "y" BoolType; InOut = false } ]
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
                Params = [ { Var = arg "x" BoolType; InOut = false }; { Var = arg "y" BoolType; InOut = false } ]
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
                        { Var = arg "x" IntType; InOut = false }
                        { Var = arg "y" IntType; InOut = false } 
                        { Var = arg "z" IntType; InOut = false } 
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
                        { Var = arg "x" IntType; InOut = false }
                        { Var = arg "y" IntType; InOut = false } 
                        { Var = arg "z" IntType; InOut = false } 
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
                Params = [ { Var = arg "b" BoolType; InOut = false }; { Var = arg "c" BoolType; InOut = false } ]
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