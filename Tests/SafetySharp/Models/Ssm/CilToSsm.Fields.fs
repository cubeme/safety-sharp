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

open System
open System.Linq
open NUnit.Framework
open Mono.Cecil
open SafetySharp.Modeling
open SafetySharp.Models
open SafetySharp.Models.Ssm
open SafetySharp.Tests

[<TestFixture>]
module ``CilToSsm Field Transformations`` =

    let private transform componentCode initCode = 
        let model = createModel (sprintf "%s class TestModel : Model { public TestModel() { SetPartitions(%s); } }" componentCode initCode)
        model.FinalizeMetadata ()
        let ssm = CilToSsm.transformModel model
        ssm.[0].Fields

    let private arg name t = Arg (name, t)
    let private local name t = Local (name, t)
    let private tmp = CilToSsm.freshLocal

    [<Test>]
    let ``component without fields`` () =
        transform "class C : Component {}" "new C()" =? []

    [<Test>]
    let ``component without fields; fields with unsupported types are ignored`` () =
        transform "class C : Component { string s; Component c; }" "new C()" =? []

    [<Test>]
    let ``component with single field`` () =
        transform "class C : Component { int _field; }" "new C()" =? [ Field (CilToSsm.renameField "_field" 0, IntType) ]

    [<Test>]
    let ``component with two fields`` () =
        transform "class C : Component { int _field1; bool _field2; }" "new C()" =? 
            [ Field (CilToSsm.renameField "_field1" 0, IntType); Field (CilToSsm.renameField "_field2" 0, BoolType) ]

    [<Test; Ignore("not yet implemented")>]
    let ``generic component with generic field of supported type`` () =
        let c = "class C<T> : Component { T _field; }"
        transform c "new C<int>()" =? [ Field (CilToSsm.renameField "_field" 0, IntType) ]
        transform c "new C<bool>()" =? [ Field (CilToSsm.renameField "_field" 0, BoolType) ]

    [<Test; Ignore("not yet implemented")>]
    let ``generic component with generic field of unsupported type`` () =
        let c = "class C<T> : Component { T _field; }"
        transform c "new C<string>()" =? []
        transform c "new C<Component>()" =? []

    [<Test>]
    let ``renaming: inherited component with non-conflicting field names`` () =
        let c = "class C : Component { int _field; } class D : C { bool _otherField; }"
        transform c "new D()" =? [ Field (CilToSsm.renameField "_field" 0, IntType); Field (CilToSsm.renameField "_otherField" 1, BoolType) ]
                                                                                            
    [<Test>]
    let ``renaming: inherited component with conflicting field names`` () =
        let c = "class C : Component { int _field1; bool _field2; } class D : C { bool _field1; bool _field2; }"
        transform c "new D()" =? 
            [ 
                Field (CilToSsm.renameField "_field1" 0, IntType)
                Field (CilToSsm.renameField "_field2" 0, BoolType) 
                Field (CilToSsm.renameField "_field1" 1, BoolType)
                Field (CilToSsm.renameField "_field2" 1, BoolType) 
            ]

    [<Test>]
    let ``renaming: inherited component with deep inheritance hierarchy`` () =
        let c = "class A : Component { int a; } class B : A { bool b1; bool b2; } class C : B { bool c; } class D : C { int d; } class E : D { bool e; }"
        transform c "new E()" =? 
            [ 
                Field (CilToSsm.renameField "a" 0, IntType)
                Field (CilToSsm.renameField "b1" 1, BoolType) 
                Field (CilToSsm.renameField "b2" 1, BoolType) 
                Field (CilToSsm.renameField "c" 2, BoolType) 
                Field (CilToSsm.renameField "d" 3, IntType) 
                Field (CilToSsm.renameField "e" 4, BoolType) 
            ]