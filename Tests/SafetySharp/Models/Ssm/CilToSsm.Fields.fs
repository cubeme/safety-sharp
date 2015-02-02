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

namespace Models.Ssm

open System
open System.Linq
open NUnit.Framework
open Mono.Cecil
open SafetySharp.Modeling
open SafetySharp.Models
open SafetySharp.Models.Ssm

[<TestFixture>]
module ``CilToSsm Field Transformations`` =

    let private transform componentCode initCode = 
        let model = TestCompilation.CreateModel (sprintf "%s class TestModel : Model { public TestModel() { SetRootComponents(%s); } }" componentCode initCode)
        model.FinalizeMetadata ()
        let ssm = CilToSsm.transformModel model
        ssm.[0].Fields

    let private arg name t = Arg (name, t)
    let private local name t = Local (name, t)
    let private tmp = CilToSsm.freshLocal
    let private field f l t i = { Var = Field (CilToSsm.makeUniqueFieldName f l, t); Init = i }

    [<Test>]
    let ``component without fields`` () =
        transform "class C : Component {}" "new C()" =? []

    [<Test>]
    let ``component without fields; fields with unsupported types are ignored`` () =
        transform "class C : Component { string s; Component c; }" "new C()" =? []

    [<Test>]
    let ``constant fields should be ignored`` () =
        transform "class C : Component { const int x = 4; }" "new C()" =? []

    [<Test>]
    let ``component with single field`` () =
        transform "class C : Component { int _field; }" "new C()" =? [ field "_field" 2 IntType [IntVal 0] ]

    [<Test>]
    let ``component with two fields`` () =
        transform "class C : Component { int _field1; bool _field2; }" "new C()" =? 
            [ field "_field1" 2 IntType [IntVal 0]; field "_field2" 2 BoolType [BoolVal false] ]

    [<Test>]
    let ``generic component with generic field of supported type`` () =
        let c = "class C<T> : Component { T _field; }"
        transform c "new C<int>()" =? [ field "_field" 2 IntType [IntVal 0] ]
        transform c "new C<bool>()" =? [ field "_field" 2 BoolType [BoolVal false] ]

    [<Test>]
    let ``generic component with generic field of unsupported type`` () =
        let c = "class C<T> : Component { T _field; }"
        transform c "new C<string>()" =? []
        transform c "new C<Component>()" =? []

    [<Test>]
    let ``renaming: inherited component with non-conflicting field names`` () =
        let c = "class C : Component { int _field; } class D : C { bool _otherfield; }"
        transform c "new D()" =? [ field "_field" 2 IntType [IntVal 0]; field "_otherfield" 3 BoolType [BoolVal false] ]
                                                                                            
    [<Test>]
    let ``renaming: inherited component with conflicting field names`` () =
        let c = "class C : Component { int _field1; bool _field2; } class D : C { bool _field1; bool _field2; }"
        transform c "new D()" =? 
            [ 
                field "_field1" 2 IntType [IntVal 0]
                field "_field2" 2 BoolType [BoolVal false]
                field "_field1" 3 BoolType [BoolVal false]
                field "_field2" 3 BoolType [BoolVal false]
            ]

    [<Test>]
    let ``renaming: inherited component with deep inheritance hierarchy`` () =
        let c = "class A : Component { int a; } class B : A { bool b1; bool b2; } class C : B { bool c; } class D : C { int d; } class E : D { bool e; }"
        transform c "new E()" =? 
            [ 
                field "a" 2 IntType [IntVal 0]
                field "b1" 3 BoolType [BoolVal false]
                field "b2" 3 BoolType [BoolVal false]
                field "c" 4 BoolType [BoolVal false]
                field "d" 5 IntType [IntVal 0] 
                field "e" 6 BoolType [BoolVal false]
            ]

    [<Test>]
    let ``field with default initial value`` () =
        transform "class X : Component { int _f; }" "new X()" =?
            [field "_f" 2 IntType [IntVal 0]]

        transform "class X : Component { bool _f; }" "new X()" =?
            [field "_f" 2 BoolType [BoolVal false]]

    [<Test>]
    let ``field with explicitly set single initial value`` ([<Range (-1, 1)>] value) =
        transform (sprintf "class X : Component { int _f = %d; }" value) "new X()" =?
            [field "_f" 2 IntType [IntVal value]]

        let value = if value = 0 then false else true
        transform (sprintf "class X : Component { bool _f = %b; }" value) "new X()" =?
            [field "_f" 2 BoolType [BoolVal value]]

    [<Test>]
    let ``field with explicitly set single initial value via constructor`` ([<Range (-1, 1)>] value) =
        transform "class X : Component { int _f; public X(int f) { _f = f; } }" (sprintf "new X(%d)" value) =?
            [field "_f" 2 IntType [IntVal value]]

        let value = if value = 0 then false else true
        transform "class X : Component { bool _f; public X(bool f) { _f = f; } }" (sprintf "new X(%b)" value) =?
            [field "_f" 2 BoolType [BoolVal value]]

    [<Test>]
    let ``field with multiple initial values`` () =
        transform "class X : Component { int _f; public X() { SetInitialValues(() => _f, -1, 0, 17); } }" "new X()" =?
            [field "_f" 2 IntType [IntVal -1; IntVal 0; IntVal 17]]

        transform "class X : Component { bool _f; public X() { SetInitialValues(() => _f, true, false); } }" "new X()" =?
            [field "_f" 2 BoolType [BoolVal true; BoolVal false]]

    [<Test>]
    let ``inherited fields with initial values`` () =
        let c = "class C : Component { int _field1 = 3; bool _field2; public C() { SetInitialValues(() => _field2, true, false); } } class D : C { bool _field1 = true; bool _field2; }"
        transform c "new D()" =? 
            [ 
                field "_field1" 2 IntType [IntVal 3]
                field "_field2" 2 BoolType [BoolVal true; BoolVal false]
                field "_field1" 3 BoolType [BoolVal true]
                field "_field2" 3 BoolType [BoolVal false]
            ]

    [<Test>]
    let ``generic fields of inherited component`` () =
        let c = "class C : Component { int b = 3; } class D<T> : C { T b; public D(params T[] v) { SetInitialValues(() => b, v); }}"
        transform c "new D<int>(16, 3, -1)" =? [field "b" 2 IntType [IntVal 3]; field "b" 3 IntType [IntVal 16; IntVal 3; IntVal -1] ]
        transform c "new D<bool>(true, false)" =? [field "b" 2 IntType [IntVal 3]; field "b" 3 BoolType [BoolVal true; BoolVal false] ]

    [<Test>]
    let ``generic fields of inherited generic component`` () =
        let c = "class C<T1, T2> : Component { T1 b; T2 c; protected C(T1 b1, T2 c2) { b = b1; c = c2; }} class D : C<int, bool> { double d = .5; public D() : base(3, true) {}}"
        transform c "new D()" =? [field "b" 2 IntType [IntVal 3]; field "c" 2 BoolType [BoolVal true]; field "d" 3 DoubleType [DoubleVal 0.5] ]

    [<Test>]
    let ``generic fields of generic inherited generic component`` () =
        let c = "class C<T> : Component { T b; public C(params T[] v) { SetInitialValues(() => b, v); } } class D<T, R> : C<T> { R b; public D(R v1, params T[] v2) : base(v2) { SetInitialValues(() => b, v1); }}"
        transform c "new D<int, bool>(false, -4, 2, 1)" =? [field "b" 2 IntType [IntVal -4; IntVal 2; IntVal 1]; field "b" 3 BoolType [BoolVal false] ]
        transform c "new D<int, bool>(true, 0)" =? [field "b" 2 IntType [IntVal 0]; field "b" 3 BoolType [BoolVal true] ]
        transform c "new D<bool, int>(17, true, false)" =? [field "b" 2 BoolType [BoolVal true; BoolVal false]; field "b" 3 IntType [IntVal 17] ]
        transform c "new D<double, double>(.5, 1.5)" =? [field "b" 2 DoubleType [DoubleVal 1.5]; field "b" 3 DoubleType [DoubleVal 0.5] ]
