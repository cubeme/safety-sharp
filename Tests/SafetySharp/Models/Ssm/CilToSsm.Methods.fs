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

namespace Models.Ssm.CilToSsm

open System
open System.Linq
open NUnit.Framework
open Mono.Cecil
open SafetySharp.Runtime.Modeling
open SafetySharp.Reflection
open SafetySharp.Models
open SafetySharp.Models.Ssm

[<TestFixture>]
module Methods =
    let private className = "TestClass"

    let private transform componentCode initCode = 
        let model = TestCompilation.CreateModel (sprintf "%s class TestModel : Model { public TestModel() { SetRootComponents(%s); } }" componentCode initCode)
        model.FinalizeMetadata ()
        let root = CilToSsm.transformModel model
        root.Subs |> List.collect (fun c -> c.Methods)

    let private transformMethod methodDefinition= 
        let csharpCode = sprintf "class %s : Component { %s }" className methodDefinition
        let compilation = TestCompilation csharpCode
        let assembly = compilation.GetAssemblyDefinition ()
        let typeDef = assembly.MainModule.GetType className
        let methodDef = typeDef.Methods.Single (fun m -> m.Name = "M")

        printfn "MSIL of method body:"
        methodDef.Body.Instructions |> Seq.iteri (printfn "%3i: %A")

        printfn ""
        printfn "Transformed method:"
        let ssm = transform (sprintf "class %s : Component { %s }" className methodDefinition) (sprintf "new %s()" className)
        let m = ssm |> Seq.find (fun m -> m.Name = methodName "M" 2 0)
        SsmToCSharp.transform m |> printfn "%s"
        m

    let private arg name t = Arg (name, t)
    let private local name t = Local (sprintf "%s%c" name Renaming.VarToken, t)
    let private field name t = Field (fieldName name 2, t)
    let private tmp = CilToSsm.freshLocal

    [<Test>]
    let ``extern method without return value and parameters should have kind required port`` () =
        transformMethod "extern void M();" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = []
                Locals = []
                Body = NopStm
                Kind = ReqPort
            }

    [<Test>]
    let ``method with enum return value and parameters`` () =
        transformMethod "enum X { A, B } X M(X x1, out X x2) { x2 = X.B; return x1; }" =?
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = [{ Var = arg "x1" IntType; Direction = In }; { Var = arg "x2" IntType; Direction = Out }]
                Locals = []
                Body = 
                    SeqStm [
                        AsgnStm (arg "x2" IntType, IntExpr 1)    
                        RetStm (Some (VarExpr (arg "x1" IntType)))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``method with enum comparison should not fail type deduction`` () =
        transformMethod "enum X { A, B } bool F() { return false; } bool M(X x, bool b) { return x != X.A && F(); }" =?
            {
                Name = methodName "M" 2 0
                Return = BoolType
                Params = [{ Var = arg "x" IntType; Direction = In }; { Var = arg "b" BoolType; Direction = In }]
                Locals = [tmp 3 0 BoolType]
                Body = IfStm (UExpr (Not, BExpr (VarExpr (arg "x" IntType), Ne, IntExpr 0)),
                              RetStm (Some (BoolExpr false)),
                              SeqStm [
                                AsgnStm (tmp 3 0 BoolType, CallExpr (methodName "F" 2 0, className, [], [], BoolType, [], false))
                                RetStm (Some (VarExpr (tmp 3 0 BoolType)))
                              ])
                Kind = ProvPort
            }

    [<Test>]
    let ``extern method with return value and parameters should have kind required port`` () =
        transformMethod "extern int M(int x);" =?
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = [ { Var = arg "x" IntType; Direction = In } ]
                Locals = []
                Body = NopStm
                Kind = ReqPort
            }

    [<Test>]
    let ``read from ref parameter`` () =
        transformMethod "int M(ref int x) { return x; }" =?
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = [ { Var = arg "x" IntType; Direction = InOut } ]
                Locals = []
                Body = RetStm (Some (VarExpr (arg "x" IntType)))
                Kind = ProvPort
            }

    [<Test>]
    let ``write to ref parameter`` () =
        transformMethod "void M(ref int x) { x = 17; }" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = [ { Var = arg "x" IntType; Direction = InOut } ]
                Locals = []
                Body = SeqStm [AsgnStm (arg "x" IntType, IntExpr 17); RetStm None]
                Kind = ProvPort
            }

    [<Test>]
    let ``write to out parameter`` () =
        transformMethod "void M(out int x) { x = 17; }" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = [ { Var = arg "x" IntType; Direction = Out } ]
                Locals = []
                Body = SeqStm [AsgnStm (arg "x" IntType, IntExpr 17); RetStm None]
                Kind = ProvPort
            }

    [<Test>]
    let ``passing field as boolean out parameter should not fail type deduction`` () =
        transformMethod "bool f; void Q(out bool x) { x = true; } void M() { Q(out f); }" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = []
                Locals = []
                Body = SeqStm [ExprStm (CallExpr (methodName "Q" 2 0, className, [BoolType], [Out], VoidType, [VarRefExpr (field "f" BoolType)], false)); RetStm None]
                Kind = ProvPort
            }

    [<Test>]
    let ``access field`` () =
        transformMethod "int _f; int M(ref int x) { _f = x; return _f; }" =?
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = [ { Var = arg "x" IntType; Direction = InOut } ]
                Locals = []
                Body = SeqStm [AsgnStm (field "_f" IntType, VarExpr (arg "x" IntType)); RetStm (Some (VarExpr (field "_f" IntType)))]
                Kind = ProvPort
            }

    [<Test>]
    let ``call static method without parameters`` () =
        transformMethod "static void F() {} void M() { F(); }" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = []
                Locals = []
                Body = SeqStm [ExprStm (TypeExpr (className, CallExpr (methodName "F" 2 0, className, [], [], VoidType, [], false))); RetStm None]
                Kind = ProvPort
            }

    [<Test>]
    let ``call static method with parameter and return value`` () =
        transformMethod "static int F(int x) { return x; } int M() { return F(4); }" =? 
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = []
                Locals = [tmp 1 0 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 1 0 IntType, TypeExpr (className, CallExpr (methodName "F" 2 0, className, [IntType], [In], IntType, [IntExpr 4], false)))
                        RetStm (Some (VarExpr (tmp 1 0 IntType)))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method on non-this target without parameters`` () =
        transformMethod "class Q { public void F() {} } Q q; void M() { q.F(); }" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = []
                Locals = []
                Body = SeqStm [ExprStm (MemberExpr (field "q" (ClassType (className + "/Q")), CallExpr (methodName "F" 1 0, "TestClass/Q", [], [], VoidType, [], true))); RetStm None]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method on non-this target with parameter and return value`` () =
        transformMethod "class Q { public int F(int x) { return x; } } Q q; int M() { return q.F(4); }" =? 
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = []
                Locals = [tmp 3 0 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 3 0 IntType, MemberExpr (field "q" (ClassType (className + "/Q")), CallExpr (methodName "F" 1 0, "TestClass/Q", [IntType], [In], IntType, [IntExpr 4], true)))
                        RetStm (Some (VarExpr (tmp 3 0 IntType)))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``call static method on other class without parameters`` () =
        transformMethod "class Q { public static void F() {} } void M() { Q.F(); }" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = []
                Locals = []
                Body = SeqStm [ExprStm (TypeExpr (className + "/Q", CallExpr (methodName "F" 1 0, "TestClass/Q", [], [], VoidType, [], false))); RetStm None]
                Kind = ProvPort
            }

    [<Test>]
    let ``call static method on other class with parameter and return value`` () =
        transformMethod "class Q { public static int F(int x) { return x; } } int M() { return Q.F(4); }" =? 
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = []
                Locals = [tmp 1 0 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 1 0 IntType, TypeExpr (className + "/Q", CallExpr (methodName "F" 1 0, "TestClass/Q", [IntType], [In], IntType, [IntExpr 4], false)))
                        RetStm (Some (VarExpr (tmp 1 0 IntType)))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``call interface method on other class without parameters`` () =
        transformMethod "interface I { void N(); } I i; void M() { i.N(); }" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = []
                Locals = []
                Body = SeqStm [ExprStm (MemberExpr (field "i" (ClassType (className + "/I")), CallExpr (methodName "N" 0 0, "TestClass/I", [], [], VoidType, [], true))); RetStm None]
                Kind = ProvPort
            }

    [<Test>]
    let ``call interface method on other class with parameter and return value`` () =
        transformMethod "interface I { int N(int n); } I i; int M() { return i.N(4); }" =? 
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = []
                Locals = [tmp 3 0 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 3 0 IntType, MemberExpr (field "i" (ClassType (className + "/I")), CallExpr (methodName "N" 0 0, "TestClass/I", [IntType], [In], IntType, [IntExpr 4], true)))
                        RetStm (Some (VarExpr (tmp 3 0 IntType)))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method without parameters`` () =
        transformMethod "void F() {} void M() { F(); }" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = []
                Locals = []
                Body = SeqStm [ExprStm (CallExpr (methodName "F" 2 0, className, [], [], VoidType, [], false)); RetStm None]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method with parameter`` () =
        transformMethod "void F(int x) {} void M() { F(4); }" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = []
                Locals = []
                Body = SeqStm [ExprStm (CallExpr (methodName "F" 2 0, className, [IntType], [In], VoidType, [IntExpr 4], false)); RetStm None]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method with ref parameter`` () =
        transformMethod "void F(ref int x) {} void M(int x) { F(ref x); }" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = [ { Var = arg "x" IntType; Direction = In } ]
                Locals = []
                Body = SeqStm [ExprStm (CallExpr (methodName "F" 2 0, className, [IntType], [InOut], VoidType, [VarRefExpr (arg "x" IntType)], false)); RetStm None]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method with out parameter`` () =
        transformMethod "void F(out int x) { x = 0; } void M(int x) { F(out x); }" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = [ { Var = arg "x" IntType; Direction = In } ]
                Locals = []
                Body = SeqStm [ExprStm (CallExpr (methodName "F" 2 0, className, [IntType], [Out], VoidType, [VarRefExpr (arg "x" IntType)], false)); RetStm None]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method ignore return`` () =
        transformMethod "int F(int x) { return x; } void M() { F(4); }" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = []
                Locals = [tmp 2 0 IntType]
                Body = SeqStm [AsgnStm (tmp 2 0 IntType, (CallExpr (methodName "F" 2 0, className, [IntType], [In], IntType, [IntExpr 4], false))); RetStm None] 
                Kind = ProvPort                   
            }

    [<Test>]
    let ``call method in binary expression`` () =
        transformMethod "int M() { return 1 + M(); }" =?
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = []
                Locals = [tmp 2 0 IntType]
                Body = 
                    SeqStm 
                        [
                            AsgnStm (tmp 2 0 IntType, CallExpr (methodName "M" 2 0, className, [], [], IntType, [], false))
                            RetStm (Some (BExpr (IntExpr 1, Add, VarExpr (tmp 2 0 IntType))))
                        ] 
                Kind = ProvPort                   
            }

    [<Test>]
    let ``call method in method parameter`` () =
        transformMethod "int M(int x) { return M(M(x)); }" =?
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = [ { Var = arg "x" IntType; Direction = In } ]
                Locals = [tmp 3 0 IntType; tmp 4 0 IntType]
                Body = 
                    SeqStm 
                        [
                            AsgnStm (tmp 3 0 IntType, CallExpr (methodName "M" 2 0, className, [IntType], [In], IntType, [VarExpr (arg "x" IntType)], false))
                            AsgnStm (tmp 4 0 IntType, CallExpr (methodName "M" 2 0, className, [IntType], [In], IntType, [VarExpr (tmp 3 0 IntType)], false))
                            RetStm (Some (VarExpr (tmp 4 0 IntType)))
                        ] 
                Kind = ProvPort                   
            }

    [<Test>]
    let ``call method in if condition`` () =
        transformMethod "bool M() { if (M()) return true; else return false; }" =?
            {
                Name = methodName "M" 2 0
                Return = BoolType
                Params = []
                Locals = [tmp 1 0 BoolType]
                Body = 
                    SeqStm 
                        [
                            AsgnStm (tmp 1 0 BoolType, CallExpr (methodName "M" 2 0, className, [], [], BoolType, [], false))
                            IfStm (
                                UExpr (Not, VarExpr (tmp 1 0 BoolType)),
                                RetStm (Some (BoolExpr false)),
                                RetStm (Some (BoolExpr true))
                            )
                        ] 
                Kind = ProvPort                   
            }

    [<Test>]
    let ``call method in ternary operator`` () =
        transformMethod "bool M() { return M() ? true : false; }" =?
            {
                Name = methodName "M" 2 0
                Return = BoolType
                Params = []
                Locals = [tmp 1 0 BoolType]
                Body = 
                    SeqStm 
                        [
                            AsgnStm (tmp 1 0 BoolType, CallExpr (methodName "M" 2 0, className, [], [], BoolType, [], false))
                            IfStm (
                                VarExpr (tmp 1 0 BoolType),
                                RetStm (Some (BoolExpr true)),
                                RetStm (Some (BoolExpr false))
                            )
                        ] 
                Kind = ProvPort                   
            }

    [<Test>]
    let ``call method ignore return within if statement`` () =
        transformMethod "int F(int x) { return x; } void M(bool b) { if (b) F(4); else F(1); }" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = [ { Var = arg "b" BoolType; Direction = In } ]
                Locals = [tmp 9 0 IntType; tmp 4 0 IntType]
                Body = 
                    IfStm (
                        UExpr (Not, VarExpr (arg "b" BoolType)),
                        SeqStm [AsgnStm (tmp 9 0 IntType, CallExpr (methodName "F" 2 0, className, [IntType], [In], IntType, [IntExpr 1], false)); RetStm None],
                        SeqStm [AsgnStm (tmp 4 0 IntType, CallExpr (methodName "F" 2 0, className, [IntType], [In], IntType, [IntExpr 4], false)); RetStm None]
                    )
                Kind = ProvPort
            }

    [<Test>]
    let ``call method with multiple parameters`` () =
        transformMethod "void F(int x, bool y, int z, bool w, bool q) {} void M(int a, bool b) { F(a, b, 2, false, true); }" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = [ { Var = arg "a" IntType; Direction = In }; { Var = arg "b" BoolType; Direction = In } ]
                Locals = []
                Body = 
                    SeqStm [
                        ExprStm (
                                         CallExpr (methodName "F" 2 0, 
                                                   className,
                                                   [IntType; BoolType; IntType; BoolType; BoolType], 
                                                   [In; In; In; In; In],
                                                   VoidType, 
                                                   [VarExpr (arg "a" IntType); VarExpr (arg "b" BoolType); IntExpr 2; BoolExpr false; BoolExpr true],
                                                   false))
                        RetStm None
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method with multiple parameters and return value`` () =
        transformMethod "int F(int x, bool y, bool z) { return 0; } int M(int a, bool b) { return F(1, false, true); }" =?
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = [ { Var = arg "a" IntType; Direction = In }; { Var = arg "b" BoolType; Direction = In } ]
                Locals = [tmp 4 0 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 4 0 IntType, 
                            CallExpr (methodName "F" 2 0, className, [IntType; BoolType; BoolType], [In; In; In], IntType, [IntExpr 1; BoolExpr false; BoolExpr true], false))
                        RetStm (Some (VarExpr (tmp 4 0 IntType)))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``method with in, inout, and out parameters`` () =
        transformMethod "double M(double x, ref bool y, out int z) { z = y ? 1 : 0; return 3.0; }" =?
            {
                Name = methodName "M" 2 0
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
                            AsgnStm (tmp 7 0 IntType, IntExpr 0)
                        )
                        AsgnStm (arg "z" IntType, VarExpr (tmp 7 0 IntType))
                        RetStm (Some (DoubleExpr 3.0))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``do not store objects on the stack to temporaries`` () =
        transformMethod "int _f; void M() { _f += (_f > 0 ? 1 : 2) + X(_f); } int X(int v) { return v; }" =?
            {
                Name = methodName "M" 2 0
                Return = VoidType
                Params = []
                Locals = [tmp 9 0 IntType; tmp 10 0 IntType; tmp 10 1 IntType; tmp 13 0 IntType]
                Body =
                    SeqStm [
                        AsgnStm (tmp 9 0 IntType, VarExpr (field "_f" IntType))
                        IfStm (
                            BExpr (VarExpr (field "_f" IntType), Gt, IntExpr 0),
                            SeqStm [
                                AsgnStm (tmp 10 0 IntType, IntExpr 1)
                                AsgnStm (tmp 10 1 IntType, VarExpr (tmp 9 0 IntType))
                            ],
                            SeqStm [
                                AsgnStm (tmp 10 0 IntType, IntExpr 2)
                                AsgnStm (tmp 10 1 IntType, VarExpr (field "_f" IntType))
                            ]
                        )
                        AsgnStm (tmp 13 0 IntType, CallExpr (methodName "X" 2 0, className, [IntType], [In], IntType, [VarExpr (field "_f" IntType)], false))
                        AsgnStm (field "_f" IntType, BExpr (VarExpr (tmp 10 1 IntType), Add, BExpr (VarExpr (tmp 10 0 IntType), Add, VarExpr (tmp 13 0 IntType))))
                        RetStm None
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``method with complex side effects`` () =
        transformMethod "void M(int z) { z *= z-- * --z; }" =?
            {
                Name = methodName "M" 2 0
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
                Kind = ProvPort
            }

    [<Test>]
    let ``method with complex side effects when parameter is byref`` () =
        transformMethod "void M(ref int z) { z *= z-- * --z; }" =?
            let local = local "__loc_0" IntType
            {
                Name = methodName "M" 2 0
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
                Kind = ProvPort
            }

    [<Test>]
    let ``method with in and inout parameters, side effects, and complex control flow`` () =
        transformMethod "void M(ref bool y, ref int z) { z = y ? z++ : ((y = !y) ? z-- : --z); }" =?
            let local0 = local "__loc_0" BoolType
            let local1 = local "__loc_1" IntType
            let argY = arg "y" BoolType
            let argZ = arg "z" IntType
            {
                Name = methodName "M" 2 0
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
                                       ]
                                   )
                            ]
                        )
                        AsgnStm (argZ, VarExpr (tmp 43 0 IntType))
                        RetStm None
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``ternary operator before return`` () =
        transformMethod "int M(int x) { var y = x > 0 ? -1 : 1; return y - 1; }" =? 
            let tmp = tmp 6 0 IntType
            let condition = BExpr (VarExpr (arg "x" IntType), Gt, IntExpr 0)
            let thenStm = AsgnStm (tmp, IntExpr -1)
            let elseStm = AsgnStm (tmp, IntExpr 1)
            let ifStm = IfStm (condition, thenStm, elseStm)
            let retStm = RetStm <| Some (BExpr (VarExpr tmp, Sub, IntExpr 1))
            { 
                Name = methodName "M" 2 0 
                Params = [ { Var = arg "x" IntType; Direction = In } ]
                Body = SeqStm [ifStm; retStm]
                Return = IntType
                Locals = [tmp]
                Kind = ProvPort
            }

    [<Test>]
    let ``ternary operator with method calls`` () =
        transformMethod "int M(int x) { return F1(false) ? F2(false) : F3(2); } bool F1(bool v) { return v; } int F2(bool x) { return 1; } int F3(int x) { return x; }" =? 
            { 
                Name = methodName "M" 2 0 
                Params = [ { Var = arg "x" IntType; Direction = In } ]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 2 0 BoolType, CallExpr (methodName "F1" 2 0, className, [BoolType], [In], BoolType, [BoolExpr false], false))
                        IfStm (
                            VarExpr (tmp 2 0 BoolType),
                            SeqStm [
                                AsgnStm (tmp 10 0 IntType, CallExpr (methodName "F2" 2 0, className, [BoolType], [In], IntType, [BoolExpr false], false))
                                RetStm (Some (VarExpr (tmp 10 0 IntType)))
                            ],
                            SeqStm [
                                AsgnStm (tmp 6 0 IntType, CallExpr (methodName "F3" 2 0, className, [IntType], [In], IntType, [IntExpr 2], false))
                                RetStm (Some (VarExpr (tmp 6 0 IntType)))
                            ]
                        )
                    ]
                Return = IntType
                Locals = [tmp 2 0 BoolType; tmp 10 0 IntType; tmp 6 0 IntType]
                Kind = ProvPort
            }

    [<Test>]
    let ``short-circuit 'or' with method calls`` () =
        transformMethod "int M(int x) { if (F1(false) || F2(1)) return 1; return -1; } bool F1(bool x) { return false; } bool F2(int x) { return false; }" =? 
            { 
                Name = methodName "M" 2 0 
                Params = [ { Var = arg "x" IntType; Direction = In } ]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 2 0 BoolType, CallExpr (methodName "F1" 2 0, className, [BoolType], [In], BoolType, [BoolExpr false], false))
                        IfStm (
                            VarExpr (tmp 2 0 BoolType),
                            RetStm (Some (IntExpr 1)),
                            SeqStm [
                                AsgnStm (tmp 6 0 BoolType, CallExpr (methodName "F2" 2 0, className, [IntType], [In], BoolType, [IntExpr 1], false))
                                IfStm (
                                    UExpr (Not, VarExpr (tmp 6 0 BoolType)),
                                    RetStm (Some (IntExpr -1)),
                                    RetStm (Some (IntExpr 1))
                                )
                            ]
                        )
                    ]
                Return = IntType
                Locals = [tmp 2 0 BoolType; tmp 6 0 BoolType]
                Kind = ProvPort
            }

    [<Test>]
    let ``short-circuit 'or' for Boolean variables and return`` () = 
        transformMethod "int M(bool x, bool y) { if (x || y) return -1; return 0; }" =? 
            let condition = UExpr (Not, BExpr (VarExpr (arg "x" BoolType), Or, VarExpr (arg "y" BoolType)))
            let thenStm = RetStm (Some (IntExpr 0))
            let elseStm = RetStm (Some (IntExpr -1))
            { 
                Name = methodName "M" 2 0 
                Params = [ { Var = arg "x" BoolType; Direction = In }; { Var = arg "y" BoolType; Direction = In } ]
                Body = IfStm (condition, thenStm, elseStm)
                Return = IntType
                Locals = []
                Kind = ProvPort
            }

    [<Test>]
    let ``short-circuit 'and' for Boolean variables and return`` () = 
        transformMethod "int M(bool x, bool y) { if (x && y) return -1; return 0; }" =? 
            let condition = UExpr (Not, BExpr (VarExpr (arg "x" BoolType), And, VarExpr (arg "y" BoolType)))
            let thenStm = RetStm (Some (IntExpr 0))
            let elseStm = RetStm (Some (IntExpr -1))
            { 
                Name = methodName "M" 2 0 
                Params = [ { Var = arg "x" BoolType; Direction = In }; { Var = arg "y" BoolType; Direction = In } ]
                Body = IfStm (condition, thenStm, elseStm)
                Return = IntType
                Locals = []
                Kind = ProvPort
            }

    [<Test>]
    let ``tenary operator with preincrement side effect`` () =
        transformMethod "void M(int x, int y, int z) { z = x > 0 ? ++y : 0; }" =? 
            let condition = BExpr (VarExpr (arg "x" IntType), Gt, IntExpr 0)
            let thenStm = 
                let assignStm1 = AsgnStm (tmp 9 0 IntType, VarExpr (arg "y" IntType))
                let assignStm2 = AsgnStm (tmp 10 0 IntType, BExpr (VarExpr (tmp 9 0 IntType), Add, IntExpr 1))
                let assignStm3 = AsgnStm (arg "y" IntType, BExpr (VarExpr (arg "y" IntType), Add, IntExpr 1))
                SeqStm [assignStm1; assignStm2; assignStm3]
            let elseStm = AsgnStm (tmp 10 0 IntType, IntExpr 0)
            let ifStm = IfStm (condition, thenStm, elseStm)
            let assignStm = AsgnStm (arg "z" IntType, VarExpr (tmp 10 0 IntType))
            { 
                Name = methodName "M" 2 0 
                Params = 
                    [ 
                        { Var = arg "x" IntType; Direction = In }
                        { Var = arg "y" IntType; Direction = In } 
                        { Var = arg "z" IntType; Direction = In } 
                    ]
                Body = SeqStm [ifStm; assignStm; RetStm None]
                Return = VoidType
                Locals = [ tmp 9 0 IntType; tmp 10 0 IntType ]
                Kind = ProvPort
            }

    [<Test>]
    let ``tenary operator with postdecrement side effect`` () =
        transformMethod "void M(int x, int y, int z) { z = x > 0 ? y-- : 0; }" =? 
            let condition = BExpr (VarExpr (arg "x" IntType), Gt, IntExpr 0)
            let thenStm = 
                let assignStm1 = AsgnStm (tmp 9 0 IntType, VarExpr (arg "y" IntType))
                let assignStm2 = AsgnStm (tmp 10 0 IntType, VarExpr (tmp 9 0 IntType))
                let assignStm3 = AsgnStm (arg "y" IntType, BExpr (VarExpr (arg "y" IntType), Sub, IntExpr 1))
                SeqStm [assignStm1; assignStm2; assignStm3]
            let elseStm = AsgnStm (tmp 10 0 IntType, IntExpr 0)
            let ifStm = IfStm (condition, thenStm, elseStm)
            let assignStm = AsgnStm (arg "z" IntType, VarExpr (tmp 10 0 IntType))
            { 
                Name = methodName "M" 2 0 
                Params = 
                    [ 
                        { Var = arg "x" IntType; Direction = In }
                        { Var = arg "y" IntType; Direction = In } 
                        { Var = arg "z" IntType; Direction = In } 
                    ]
                Body = SeqStm [ifStm; assignStm; RetStm None]
                Return = VoidType
                Locals = [ tmp 9 0 IntType; tmp 10 0 IntType ]
                Kind = ProvPort
            }

    [<Test>]
    let ``nested ternary operator`` () =
        transformMethod "int M(bool b, bool c) { var x = 1 + (b ? (c ? 4 : 2) : 3); return x; }" =? 
            { 
                Name = methodName "M" 2 0 
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
                                    ]
                                )
                            ],
                            SeqStm [
                                AsgnStm (tmp 10 0 IntType, IntExpr 3)
                                AsgnStm (tmp 10 1 IntType, IntExpr 1)
                            ]
                        )
                        RetStm (Some (BExpr (VarExpr (tmp 10 1 IntType), Add, VarExpr (tmp 10 0 IntType))))
                    ]
                Return = IntType
                Locals = [ tmp 5 0 IntType; tmp 9 0 IntType; tmp 10 0 IntType; tmp 10 1 IntType ]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method with local byref parameter should store local in temporary`` () =
        transformMethod "int F(ref int x) { return x; } int M() { int x = 0; return x + F(ref x); }" =?
            let local = local "__loc_0" IntType
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = []
                Locals = [local; tmp 5 0 IntType; tmp 5 1 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (local, IntExpr 0)
                        AsgnStm (tmp 5 0 IntType, VarExpr local)
                        AsgnStm (tmp 5 1 IntType, CallExpr (methodName "F" 2 0, className, [IntType], [InOut], IntType, [VarRefExpr local], false))
                        RetStm (Some (BExpr (VarExpr (tmp 5 0 IntType), Add, VarExpr (tmp 5 1 IntType))))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method with field parameter should store field in temporary`` () =
        transformMethod "int F(int x) { return x; } int f; int M() { return f + F(f); }" =?
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = []
                Locals = [tmp 5 0 IntType; tmp 5 1 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 5 0 IntType, VarExpr (field "f" IntType))
                        AsgnStm (tmp 5 1 IntType, CallExpr (methodName "F" 2 0, className, [IntType], [In], IntType, [VarExpr (field "f" IntType)], false))
                        RetStm (Some (BExpr (VarExpr (tmp 5 0 IntType), Add, VarExpr (tmp 5 1 IntType))))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method with integer readonly field parameter should inline field`` () =
        transformMethod "int F(int x) { return x; } readonly int f = 4; int M() { return f + F(f); }" =?
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = []
                Locals = [tmp 5 0 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 5 0 IntType, CallExpr (methodName "F" 2 0, className, [IntType], [In], IntType, [IntExpr 4], false))
                        RetStm (Some (BExpr (IntExpr 4, Add, VarExpr (tmp 5 0 IntType))))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method with double readonly field parameter should inline field`` () =
        transformMethod "double F(double x) { return x; } readonly double f = .5; double M() { return f + F(f); }" =?
            {
                Name = methodName "M" 2 0
                Return = DoubleType
                Params = []
                Locals = [tmp 5 0 DoubleType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 5 0 DoubleType, CallExpr (methodName "F" 2 0, className, [DoubleType], [In], DoubleType, [DoubleExpr 0.5], false))
                        RetStm (Some (BExpr (DoubleExpr 0.5, Add, VarExpr (tmp 5 0 DoubleType))))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method with boolean readonly field parameter should inline field`` () =
        transformMethod "bool F(bool x) { return x; } readonly bool f = true; bool M() { return f & F(f); }" =?
            {
                Name = methodName "M" 2 0
                Return = BoolType
                Params = []
                Locals = [tmp 5 0 BoolType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 5 0 BoolType, CallExpr (methodName "F" 2 0, className, [BoolType], [In], BoolType, [BoolExpr true], false))
                        RetStm (Some (BExpr (BoolExpr true, And, VarExpr (tmp 5 0 BoolType))))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method with const field parameter should inline field value`` () =
        transformMethod "int F(int x) { return x; } const int f = 4; int M() { return f + F(f); }" =?
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = []
                Locals = [tmp 3 0 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 3 0 IntType, CallExpr (methodName "F" 2 0, className, [IntType], [In], IntType, [IntExpr 4], false))
                        RetStm (Some (BExpr (IntExpr 4, Add, VarExpr (tmp 3 0 IntType))))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method with field byref parameter should store field in temporary`` () =
        transformMethod "int F(ref int x) { return x; } int f; int M() { return f + F(ref f); }" =?
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = []
                Locals = [tmp 5 0 IntType; tmp 5 1 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 5 0 IntType, VarExpr (field "f" IntType))
                        AsgnStm (tmp 5 1 IntType, CallExpr (methodName "F" 2 0, className, [IntType], [InOut], IntType, [VarRefExpr (field "f" IntType)], false))
                        RetStm (Some (BExpr (VarExpr (tmp 5 0 IntType), Add, VarExpr (tmp 5 1 IntType))))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method with value arg byref parameter should store arg in temporary`` () =
        transformMethod "int F(ref int x) { return x; } int M(int x) { return x + F(ref x); }" =?
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = [ { Var = arg "x" IntType; Direction = In } ]
                Locals = [tmp 3 0 IntType; tmp 3 1 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 3 0 IntType, VarExpr (arg "x" IntType))
                        AsgnStm (tmp 3 1 IntType, CallExpr (methodName "F" 2 0, className, [IntType], [InOut], IntType, [VarRefExpr (arg "x" IntType)], false))
                        RetStm (Some (BExpr (VarExpr (tmp 3 0 IntType), Add, VarExpr (tmp 3 1 IntType))))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``call method with byref arg byref parameter should store arg in temporary`` () =
        transformMethod "int F(ref int x) { return x; } int M(ref int x) { return x + F(ref x); }" =?
            {
                Name = methodName "M" 2 0
                Return = IntType
                Params = [ { Var = arg "x" IntType; Direction = InOut } ]
                Locals = [tmp 4 0 IntType; tmp 4 1 IntType]
                Body = 
                    SeqStm [
                        AsgnStm (tmp 4 0 IntType, VarExpr (arg "x" IntType))
                        AsgnStm (tmp 4 1 IntType, CallExpr (methodName "F" 2 0, className, [IntType], [InOut], IntType, [VarRefExpr (arg "x" IntType)], false))
                        RetStm (Some (BExpr (VarExpr (tmp 4 0 IntType), Add, VarExpr (tmp 4 1 IntType))))
                    ]
                Kind = ProvPort
            }

    [<Test>]
    let ``renaming: overloaded methods without inheritance`` () =
        transform "class X : Component { void M() { } bool M(int i) { return true; } int M(bool b) { return 1; }}" "new X()" =?
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "M" 2 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                }
                {
                    Name = methodName "M" 2 1
                    Return = BoolType
                    Params = [ { Var = arg "i" IntType; Direction = In } ]
                    Locals = []
                    Body = RetStm (Some (BoolExpr true))
                    Kind = ProvPort
                }
                {
                    Name = methodName "M" 2 2
                    Return = IntType
                    Params = [ { Var = arg "b" BoolType; Direction = In } ]
                    Locals = []
                    Body = RetStm (Some (IntExpr 1))
                    Kind = ProvPort
                }
            ]

    [<Test>]
    let ``renaming: inherited component with non-conflicting field names`` () =
        let c = "class C : Component { void M() {} } class D : C { bool N(bool n) { return n; } }"
        transform c "new D()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "M" 2 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                }
                {
                    Name = methodName "N" 3 0
                    Return = BoolType
                    Params = [ { Var = arg "n" BoolType; Direction = In } ]
                    Locals = []
                    Body = RetStm (Some (VarExpr (arg "n" BoolType)))
                    Kind = ProvPort
                }
            ]
                                                                                            
    [<Test>]
    let ``renaming: inherited component with conflicting and overloaded methods`` () =
        let c = "class C : Component { void M() {} void M(int i) {} } class D : C { void M() {} void M(bool b) {} }"
        transform c "new D()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "M" 2 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                }
                {
                    Name = methodName "M" 2 1
                    Return = VoidType
                    Params = [ { Var = arg "i" IntType; Direction = In } ]
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                }
                {
                    Name = methodName "M" 3 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                }
                {
                    Name = methodName "M" 3 1
                    Return = VoidType
                    Params = [ { Var = arg "b" BoolType; Direction = In } ]
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                }
            ]

    [<Test>]
    let ``renaming: inherited component with deep inheritance hierarchy`` () =
        let c = "class A : Component { void M() {} } class B : A { } class C : B { void N() {} } class D : C { void M() {} } class E : D { void Q() {} }"
        transform c "new E()" =? 
             [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "M" 2 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                }
                {
                    Name = methodName "N" 4 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                }
                {
                    Name = methodName "M" 5 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                }
                {
                    Name = methodName "Q" 6 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                }
            ]

    [<Test>]
    let ``renaming: access to renamed fields`` () =
        let c = "class A : Component {} class B : A { int x; int M() { return x; } }"
        transform c "new B()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "M" 3 0
                    Return = IntType
                    Params = []
                    Locals = []
                    Body = RetStm (Some (VarExpr (field (fieldName "x" 1) IntType)))
                    Kind = ProvPort
                } 
            ]

    [<Test>]
    let ``renaming: access to renamed method of same component`` () =
        let c = "class A : Component {} class B : A { int M(int x) { return x; } int M() { return M(1); } }"
        transform c "new B()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "M" 3 0
                    Return = IntType
                    Params = [ { Var = arg "x" IntType; Direction = In } ]
                    Locals = []
                    Body = RetStm (Some (VarExpr (arg "x" IntType)))
                    Kind = ProvPort
                } 
                {
                    Name = methodName "M" 3 1
                    Return = IntType
                    Params = []
                    Locals = [tmp 2 0 IntType]
                    Body = 
                        SeqStm [
                            AsgnStm (tmp 2 0 IntType, 
                                CallExpr (methodName "M" 3 0, "B", [IntType], [In], IntType, [IntExpr 1], false))
                            RetStm (Some (VarExpr (tmp 2 0 IntType)))
                    ]
                    Kind = ProvPort
                } 
            ]

    [<Test>]
    let ``renaming: access to renamed method of other component`` () =
        let c = "class A : Component {} class B : A { public void M() {} } class C : Component { B b; void M() { b.M(); } }"
        transform c "new B(), new C()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "M" 3 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                } 
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "M" 2 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = 
                        SeqStm [
                            ExprStm (MemberExpr (field "b" (ClassType "B"), CallExpr (methodName "M" 3 0, "B", [], [], VoidType, [], true)))
                            RetStm None
                        ]
                    Kind = ProvPort
                } 
            ]

    [<Test>]
    let ``renaming: method redefinition`` () =
        let c = "class A : Component { public void M() {} } class B : A { public new void M() { base.M(); } }"
        transform c "new B()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "M" 2 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                } 
                {
                    Name = methodName "M" 3 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = SeqStm [ExprStm (CallExpr (methodName "M" 2 0, "A", [], [], VoidType, [], false)); RetStm None]
                    Kind = ProvPort
                } 
            ]

    [<Test>]
    let ``renaming: method overloading chain`` () =
        let c = "class A : Component { public virtual void M() {} } class B : A { public override void M() { base.M(); } } class C : B { public override void M() { base.M(); } }"
        transform c "new C()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "M" 2 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None                    
                    Kind = ProvPort
                } 
                {
                    Name = methodName "M" 3 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = SeqStm [ExprStm (CallExpr (methodName "M" 2 0, "A", [], [], VoidType, [], false)); RetStm None]                   
                    Kind = ProvPort
                } 
                {
                    Name = methodName "M" 4 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = SeqStm [ExprStm (CallExpr (methodName "M" 3 0, "B", [], [], VoidType, [], false)); RetStm None]
                    Kind = ProvPort
                } 
            ]

    [<Test>]
    let ``abstract method has an empty body`` () =
        let c = "abstract class A : Component { public abstract void M(); } class B : A { public override void M() { } }"
        transform c "new B()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "M" 2 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = NopStm
                    Kind = ProvPort
                } 
                {
                    Name = methodName "M" 3 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                } 
            ]

    [<Test>]
    let ``call method with integer readonly field parameter defined by base class should inline field`` () =
        let c = "class A : Component { protected readonly int f = 4; } class B : A { int M() { return f; } }"
        transform c "new B()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "M" 3 0
                    Return = IntType
                    Params = []
                    Locals = []
                    Body = RetStm (Some (IntExpr 4))
                    Kind = ProvPort
                }
            ]

    [<Test>]
    let ``method using generic parameters of enclosing class`` () =
        let c = "class A<T1, T2> : Component { T1 f; T1 M(T2 p) { M(p); return f; } }"
        transform c "new A<int, bool>()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "M" 2 0
                    Return = IntType
                    Params = [{ Var = arg "p" BoolType; Direction = In }]
                    Locals = [tmp 2 0 IntType]
                    Body = 
                        SeqStm
                            [
                                AsgnStm (tmp 2 0 IntType, CallExpr (methodName "M" 2 0, "A`2<T1,T2>", [BoolType], [In], IntType, [VarExpr (arg "p" BoolType)], false))
                                RetStm (Some (VarExpr (field "f" IntType)))
                            ]
                    Kind = ProvPort
                }
            ]

    [<Test>]
    let ``method calling method of generic base`` () =
        let c = "class A<T1, T2> : Component { T1 f; public T1 M(T2 p) { return f; } } class B : A<bool, int> { bool N(int x) { return M(x); } }"
        transform c "new B()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "M" 2 0
                    Return = BoolType
                    Params = [{ Var = arg "p" IntType; Direction = In }]
                    Locals = []
                    Body = RetStm (Some (VarExpr (field "f" BoolType)))
                    Kind = ProvPort
                }
                {
                    Name = methodName "N" 3 0
                    Return = BoolType
                    Params = [{ Var = arg "x" IntType; Direction = In }]
                    Locals = [tmp 2 0 BoolType]
                    Body = 
                        SeqStm
                            [
                                AsgnStm (tmp 2 0 BoolType, CallExpr (methodName "M" 2 0, "A`2<System.Boolean,System.Int32>", [IntType], [In], BoolType, [VarExpr (arg "x" IntType)], false))
                                RetStm (Some (VarExpr (tmp 2 0 BoolType)))
                            ]
                    Kind = ProvPort
                }
            ]

    [<Test>]
    let ``method of generic type calling method of generic base`` () =
        let c = "class A<T1, T2> : Component { T1 f; public T1 M(T2 p) { return f; } } class B<T1> : A<T1, int> { T1 N(int x) { return M(x); } }"
        transform c "new B<bool>()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "M" 2 0
                    Return = BoolType
                    Params = [{ Var = arg "p" IntType; Direction = In }]
                    Locals = []
                    Body = RetStm (Some (VarExpr (field "f" BoolType)))
                    Kind = ProvPort
                }
                {
                    Name = methodName "N" 3 0
                    Return = BoolType
                    Params = [{ Var = arg "x" IntType; Direction = In }]
                    Locals = [tmp 2 0 BoolType]
                    Body = 
                        SeqStm
                            [
                                AsgnStm (tmp 2 0 BoolType, CallExpr (methodName "M" 2 0, "A`2<T1,System.Int32>", [IntType], [In], BoolType, [VarExpr (arg "x" IntType)], false))
                                RetStm (Some (VarExpr (tmp 2 0 BoolType)))
                            ]
                    Kind = ProvPort
                }
            ]

    [<Test>]
    let ``method calling method of generic subcomponent`` () =
        let c = "class A<T1, T2> : Component { T1 f; public T1 M(T2 p) { return f; } } class B : Component { A<bool, int> a = new A<bool, int>(); bool N(int x) { return a.M(x); } }"
        transform c "new B()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "N" 2 0
                    Return = BoolType
                    Params = [{ Var = arg "x" IntType; Direction = In }]
                    Locals = [tmp 3 0 BoolType]
                    Body = 
                        SeqStm
                            [
                                AsgnStm (tmp 3 0 BoolType, MemberExpr (Field ("R.B0@0.a@0", ClassType "A`2<System.Boolean,System.Int32>"), CallExpr (methodName "M" 2 0, "A`2<System.Boolean,System.Int32>", [IntType], [In], BoolType, [VarExpr (arg "x" IntType)], true)))
                                RetStm (Some (VarExpr (tmp 3 0 BoolType)))
                            ]
                    Kind = ProvPort
                }
            ]

    [<Test>]
    let ``method of generic type calling method of generic subcomponent`` () =
        let c = "class A<T1, T2> : Component { T1 f; public T1 M(T2 p) { return f; } } class B<T1> : Component { A<T1, int> a = new A<T1, int>(); T1 N(int x) { return a.M(x); } }"
        transform c "new B<bool>()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "N" 2 0
                    Return = BoolType
                    Params = [{ Var = arg "x" IntType; Direction = In }]
                    Locals = [tmp 3 0 BoolType]
                    Body = 
                        SeqStm
                            [
                                AsgnStm (tmp 3 0 BoolType, MemberExpr (Field ("R.B`10@0.a@0", ClassType "A`2<T1,System.Int32>"), CallExpr (methodName "M" 2 0, "A`2<T1,System.Int32>", [IntType], [In], BoolType, [VarExpr (arg "x" IntType)], true)))
                                RetStm (Some (VarExpr (tmp 3 0 BoolType)))
                            ]
                    Kind = ProvPort
                }
            ]

    [<Test>]
    let ``method of generic type calling method of generic subcomponent via generic constraint`` () =
        let c = "interface I<T1, T2> { T1 M(T2 p); } class A<T1, T2> : Component, I<T1, T2> { T1 f; public T1 M(T2 p) { return f; } } class B<T, T1, T2> : Component where T : I<T1, T2>, new() { T a = new T(); T1 N(T2 x) { return a.M(x); } }"
        transform c "new B<A<bool, int>, bool, int>()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "N" 2 0
                    Return = BoolType
                    Params = [{ Var = arg "x" IntType; Direction = In }]
                    Locals = [tmp 4 0 BoolType]
                    Body = 
                        SeqStm
                            [
                                AsgnStm (tmp 4 0 BoolType, MemberExpr (Field (fieldName "a" 2, ClassType "A`2<System.Boolean,System.Int32>"), CallExpr (methodName "M" 0 0, "I`2<T1,T2>", [IntType], [In], BoolType, [VarExpr (arg "x" IntType)], true)))
                                RetStm (Some (VarExpr (tmp 4 0 BoolType)))
                            ]
                    Kind = ProvPort
                }
            ]

    [<Test>]
    let ``step method: simple override`` () =
        let c = "class C : Component { public override void Update() {} }"
        transform c "new C()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "Update" 2 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = Step
                }
            ]

    [<Test>]
    let ``step method: inherited override`` () =
        let c = "class C : Component {} class D : C { public override void Update() {} }"
        transform c "new D()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "Update" 3 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = Step
                }
            ]

    [<Test>]
    let ``step method: inherited double override and base call`` () =
        let c = "class C : Component { public override void Update() { base.Update(); } } class D : C { public override void Update () { base.Update(); } }"
        transform c "new D()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "Update" 2 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = SeqStm [ExprStm (CallExpr (methodName "Update" 1 0, "SafetySharp.Runtime.Modeling.Component", [], [], VoidType, [], false)); RetStm None]
                    Kind = Step
                }
                {
                    Name = methodName "Update" 3 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = SeqStm [ExprStm (CallExpr (methodName "Update" 2 0, "C", [], [], VoidType, [], false)); RetStm None]
                    Kind = Step
                }
            ]

    [<Test>]
    let ``step method: non-override as required port`` () =
        let c = "class C : Component { public extern new void Update(); }"
        transform c "new C()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "Update" 2 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = NopStm
                    Kind = ReqPort
                }
            ]

    [<Test>]
    let ``step method: non-override as provided port`` () =
        let c = "class C : Component { public new void Update() {} }"
        transform c "new C()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "Update" 2 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                }
            ]

    [<Test>]
    let ``step method: inherited non-override`` () =
        let c = "class C : Component { public new void Update() {} } class D : C { }"
        transform c "new D()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "Update" 2 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                }
            ]

    [<Test>]
    let ``step method: inherited overridden non-override`` () =
        let c = "class C : Component { public new virtual void Update() {} } class D : C { public override void Update() {} }"
        transform c "new D()" =? 
            [
                Ssm.BaseUpdateMethod
                {
                    Name = methodName "Update" 2 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                }
                {
                    Name = methodName "Update" 3 0
                    Return = VoidType
                    Params = []
                    Locals = []
                    Body = RetStm None
                    Kind = ProvPort
                }
            ]