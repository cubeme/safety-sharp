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
    let private field name t = Field (name, t)
    let private tmp = CilToSsm.freshLocal

    [<Test>]
    let ``read from ref parameter`` () =
        transform "int M(ref int x) { return x; }" =?
            {
                Name = "M"
                Return = IntType
                Params = [ { Var = arg "x" IntType; Direction = InOut } ]
                Locals = []
                Body = RetStm (Some (VarExpr (arg "x" IntType)))
            }

    [<Test>]
    let ``write to ref parameter`` () =
        transform "void M(ref int x) { x = 17; }" =?
            {
                Name = "M"
                Return = VoidType
                Params = [ { Var = arg "x" IntType; Direction = InOut } ]
                Locals = []
                Body = SeqStm [AsgnStm (arg "x" IntType, IntExpr 17); RetStm None]
            }

    [<Test>]
    let ``write to out parameter`` () =
        transform "void M(out int x) { x = 17; }" =?
            {
                Name = "M"
                Return = VoidType
                Params = [ { Var = arg "x" IntType; Direction = Out } ]
                Locals = []
                Body = SeqStm [AsgnStm (arg "x" IntType, IntExpr 17); RetStm None]
            }

    [<Test>]
    let ``access field`` () =
        transform "int _f; int M(ref int x) { _f = x; return _f; }" =?
            {
                Name = "M"
                Return = IntType
                Params = [ { Var = arg "x" IntType; Direction = InOut } ]
                Locals = []
                Body = SeqStm [AsgnStm (field "_f" IntType, VarExpr (arg "x" IntType)); RetStm (Some (VarExpr (field "_f" IntType)))]
            }

    [<Test>]
    let ``call method without parameters`` () =
        transform "void F() {} void M() { F(); }" =?
            {
                Name = "M"
                Return = VoidType
                Params = []
                Locals = []
                Body = SeqStm [CallStm ("F", [], [], VoidType, []); RetStm None]
            }

    [<Test>]
    let ``call method with parameter`` () =
        transform "void F(int x) {} void M() { F(4); }" =?
            {
                Name = "M"
                Return = VoidType
                Params = []
                Locals = []
                Body = SeqStm [CallStm ("F", [IntType], [In], VoidType, [IntExpr 4]); RetStm None]
            }

    [<Test>]
    let ``call method with ref parameter`` () =
        transform "void F(ref int x) {} void M(int x) { F(ref x); }" =?
            {
                Name = "M"
                Return = VoidType
                Params = [ { Var = arg "x" IntType; Direction = In } ]
                Locals = []
                Body = SeqStm [CallStm ("F", [IntType], [InOut], VoidType, [VarRefExpr (arg "x" IntType)]); RetStm None]
            }

    [<Test>]
    let ``call method with out parameter`` () =
        transform "void F(out int x) { x = 0; } void M(int x) { F(out x); }" =?
            {
                Name = "M"
                Return = VoidType
                Params = [ { Var = arg "x" IntType; Direction = In } ]
                Locals = []
                Body = SeqStm [CallStm ("F", [IntType], [Out], VoidType, [VarRefExpr (arg "x" IntType)]); RetStm None]
            }

    [<Test>]
    let ``call method ignore return`` () =
        transform "int F(int x) { return x; } void M() { F(4); }" =?
            {
                Name = "M"
                Return = VoidType
                Params = []
                Locals = [tmp 2 0 IntType]
                Body = SeqStm [AsgnStm (tmp 2 0 IntType, CallExpr ("F", [IntType], [In], IntType, [IntExpr 4])); RetStm None]                    
            }

    [<Test>]
    let ``call method ignore return within if statement`` () =
        transform "int F(int x) { return x; } void M(bool b) { if (b) F(4); else F(1); }" =?
            {
                Name = "M"
                Return = VoidType
                Params = [ { Var = arg "b" BoolType; Direction = In } ]
                Locals = [tmp 9 0 IntType; tmp 4 0 IntType]
                Body = 
                    IfStm (
                        UExpr (Not, VarExpr (arg "b" BoolType)),
                        SeqStm [AsgnStm (tmp 9 0 IntType, CallExpr ("F", [IntType], [In], IntType, [IntExpr 1])); RetStm None],
                        SeqStm [AsgnStm (tmp 4 0 IntType, CallExpr ("F", [IntType], [In], IntType, [IntExpr 4])); RetStm None] |> Some
                    )
            }

    [<Test>]
    let ``call method with multiple parameters`` () =
        transform "void F(int x, bool y, int z, bool w, bool q) {} void M(int a, bool b) { F(a, b, 2, false, true); }" =?
            {
                Name = "M"
                Return = VoidType
                Params = [ { Var = arg "a" IntType; Direction = In }; { Var = arg "b" BoolType; Direction = In } ]
                Locals = []
                Body = 
                    SeqStm [
                        CallStm ("F", 
                            [IntType; BoolType; IntType; BoolType; BoolType], 
                            [In; In; In; In; In],
                            VoidType, 
                            [VarExpr (arg "a" IntType); VarExpr (arg "b" BoolType); IntExpr 2; BoolExpr false; BoolExpr true]
                        )
                        RetStm None
                    ]
            }

    [<Test>]
    let ``call method with multiple parameters and return value`` () =
        transform "int F(int x, bool y, bool z) { return 0; } int M(int a, bool b) { return F(1, false, true); }" =?
            {
                Name = "M"
                Return = IntType
                Params = [ { Var = arg "a" IntType; Direction = In }; { Var = arg "b" BoolType; Direction = In } ]
                Locals = [tmp 4 0 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 4 0 IntType, 
                            CallExpr ("F", [IntType; BoolType; BoolType], [In; In; In], IntType, [IntExpr 1; BoolExpr false; BoolExpr true]))
                        RetStm (Some (VarExpr (tmp 4 0 IntType)))
                    ]
            }

    [<Test>]
    let ``method with in, inout, and out parameters`` () =
        transform "double M(double x, ref bool y, out int z) { z = y ? 1 : 0; return 3.0; }" =?
            {
                Name = "M"
                Return = DoubleType
                Params = 
                    [ 
                        { Var = arg "x" DoubleType; Direction = In }
                        { Var = arg "y" BoolType; Direction = InOut } 
                        { Var = arg "z" IntType; Direction = Out } 
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
                Return = VoidType
                Params = [ { Var = arg "z" IntType; Direction = In } ]
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
                Return = VoidType
                Params = [ { Var = arg "z" IntType; Direction = InOut } ]
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
                Return = VoidType
                Params = [ { Var = arg "y" BoolType; Direction = InOut }; { Var = arg "z" IntType; Direction = InOut } ]
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
                Params = [ { Var = arg "x" IntType; Direction = In } ]
                Body = SeqStm [ifStm; retStm]
                Return = IntType
                Locals = [tmp]
            }

    [<Test>]
    let ``ternary operator with method calls`` () =
        transform "int M(int x) { return F1(false) ? F2(false) : F3(2); } bool F1(bool v) { return v; } int F2(bool x) { return 1; } int F3(int x) { return x; }" =? 
            { 
                Name = "M" 
                Params = [ { Var = arg "x" IntType; Direction = In } ]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 2 0 BoolType, CallExpr ("F1", [BoolType], [In], BoolType, [BoolExpr false]))
                        IfStm (
                            VarExpr (tmp 2 0 BoolType),
                            SeqStm [
                                AsgnStm (tmp 10 0 IntType, CallExpr ("F2", [BoolType], [In], IntType, [BoolExpr false]))
                                RetStm (Some (VarExpr (tmp 10 0 IntType)))
                            ],
                            SeqStm [
                                AsgnStm (tmp 6 0 IntType, CallExpr ("F3", [IntType], [In], IntType, [IntExpr 2]))
                                RetStm (Some (VarExpr (tmp 6 0 IntType)))
                            ] |> Some
                        )
                    ]
                Return = IntType
                Locals = [tmp 2 0 BoolType; tmp 10 0 IntType; tmp 6 0 IntType]
            }

    [<Test>]
    let ``short-circuit 'or' with method calls`` () =
        transform "int M(int x) { if (F1(false) || F2(1)) return 1; return -1; } bool F1(bool x) { return false; } bool F2(int x) { return false; }" =? 
            { 
                Name = "M" 
                Params = [ { Var = arg "x" IntType; Direction = In } ]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 2 0 BoolType, CallExpr ("F1", [BoolType], [In], BoolType, [BoolExpr false]))
                        IfStm (
                            VarExpr (tmp 2 0 BoolType),
                            RetStm (Some (IntExpr 1)),
                            SeqStm [
                                AsgnStm (tmp 6 0 BoolType, CallExpr ("F2", [IntType], [In], BoolType, [IntExpr 1]))
                                IfStm (
                                    UExpr (Not, VarExpr (tmp 6 0 BoolType)),
                                    RetStm (Some (IntExpr -1)),
                                    RetStm (Some (IntExpr 1)) |> Some
                                )
                            ] |> Some
                        )
                    ]
                Return = IntType
                Locals = [tmp 2 0 BoolType; tmp 6 0 BoolType]
            }

    [<Test>]
    let ``short-circuit 'or' for Boolean variables and return`` () = 
        transform "int M(bool x, bool y) { if (x || y) return -1; return 0; }" =? 
            let condition = UExpr (Not, BExpr (VarExpr (arg "x" BoolType), Or, VarExpr (arg "y" BoolType)))
            let thenStm = RetStm (Some (IntExpr 0))
            let elseStm = RetStm (Some (IntExpr -1))
            { 
                Name = "M" 
                Params = [ { Var = arg "x" BoolType; Direction = In }; { Var = arg "y" BoolType; Direction = In } ]
                Body = IfStm (condition, thenStm, Some elseStm)
                Return = IntType
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
                Params = [ { Var = arg "x" BoolType; Direction = In }; { Var = arg "y" BoolType; Direction = In } ]
                Body = IfStm (condition, thenStm, Some elseStm)
                Return = IntType
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
                        { Var = arg "x" IntType; Direction = In }
                        { Var = arg "y" IntType; Direction = In } 
                        { Var = arg "z" IntType; Direction = In } 
                    ]
                Body = SeqStm [ifStm; assignStm; RetStm None]
                Return = VoidType
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
                        { Var = arg "x" IntType; Direction = In }
                        { Var = arg "y" IntType; Direction = In } 
                        { Var = arg "z" IntType; Direction = In } 
                    ]
                Body = SeqStm [ifStm; assignStm; RetStm None]
                Return = VoidType
                Locals = [ tmp 9 0 IntType; tmp 10 0 IntType ]
            }

    [<Test>]
    let ``nested ternary operator`` () =
        transform "int M(bool b, bool c) { var x = 1 + (b ? (c ? 4 : 2) : 3); return x; }" =? 
            { 
                Name = "M" 
                Params = [ { Var = arg "b" BoolType; Direction = In }; { Var = arg "c" BoolType; Direction = In } ]
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
                Return = IntType
                Locals = [ tmp 5 0 IntType; tmp 9 0 IntType; tmp 10 0 IntType; tmp 10 1 IntType ]
            }

    [<Test>]
    let ``call method with local byref parameter should store local in temporary`` () =
        transform "int F(ref int x) { return x; } int M() { int x = 0; return x + F(ref x); }" =?
            let local = local "__loc_0" IntType
            {
                Name = "M"
                Return = IntType
                Params = []
                Locals = [local; tmp 5 0 IntType; tmp 5 1 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (local, IntExpr 0)
                        AsgnStm (tmp 5 0 IntType, VarExpr local)
                        AsgnStm (tmp 5 1 IntType, CallExpr ("F", [IntType], [InOut], IntType, [VarRefExpr local]))
                        RetStm (Some (BExpr (VarExpr (tmp 5 0 IntType), Add, VarExpr (tmp 5 1 IntType))))
                    ]
            }

    [<Test>]
    let ``call method with field byref parameter should store local in temporary`` () =
        transform "int F(ref int x) { return x; } int f; int M() { return f + F(ref f); }" =?
            {
                Name = "M"
                Return = IntType
                Params = []
                Locals = [tmp 5 0 IntType; tmp 5 1 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 5 0 IntType, VarExpr (field "f" IntType))
                        AsgnStm (tmp 5 1 IntType, CallExpr ("F", [IntType], [InOut], IntType, [VarRefExpr (field "f" IntType)]))
                        RetStm (Some (BExpr (VarExpr (tmp 5 0 IntType), Add, VarExpr (tmp 5 1 IntType))))
                    ]
            }

    [<Test>]
    let ``call method with value arg byref parameter should store local in temporary`` () =
        transform "int F(ref int x) { return x; } int M(int x) { return x + F(ref x); }" =?
            {
                Name = "M"
                Return = IntType
                Params = [ { Var = arg "x" IntType; Direction = In } ]
                Locals = [tmp 3 0 IntType; tmp 3 1 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 3 0 IntType, VarExpr (arg "x" IntType))
                        AsgnStm (tmp 3 1 IntType, CallExpr ("F", [IntType], [InOut], IntType, [VarRefExpr (arg "x" IntType)]))
                        RetStm (Some (BExpr (VarExpr (tmp 3 0 IntType), Add, VarExpr (tmp 3 1 IntType))))
                    ]
            }

    [<Test>]
    let ``call method with byref arg byref parameter should store local in temporary`` () =
        transform "int F(ref int x) { return x; } int M(ref int x) { return x + F(ref x); }" =?
            {
                Name = "M"
                Return = IntType
                Params = [ { Var = arg "x" IntType; Direction = InOut } ]
                Locals = [tmp 4 0 IntType; tmp 4 1 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 4 0 IntType, VarExpr (arg "x" IntType))
                        AsgnStm (tmp 4 1 IntType, CallExpr ("F", [IntType], [InOut], IntType, [VarRefExpr (arg "x" IntType)]))
                        RetStm (Some (BExpr (VarExpr (tmp 4 0 IntType), Add, VarExpr (tmp 4 1 IntType))))
                    ]
            }