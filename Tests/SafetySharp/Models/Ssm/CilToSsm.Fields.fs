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
        ssm.Fields

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
        transform "class C : Component { int _field; }" "new C()" =? [ Field ("_field", IntType) ]

    [<Test>]
    let ``component with two fields`` () =
        transform "class C : Component { int _field1; bool _field2; }" "new C()" =? 
            [ Field ("_field1", IntType); Field ("_field2", BoolType) ]

    [<Test; Ignore("not yet implemented")>]
    let ``generic component with generic field of supported type`` () =
        let c = "class C<T> : Component { T _field; }"
        transform c "new C<int>()" =? [ Field ("_field", IntType) ]
        transform c "new C<bool>()" =? [ Field ("_field", BoolType) ]

    [<Test; Ignore("not yet implemented")>]
    let ``generic component with generic field of unsupported type`` () =
        let c = "class C<T> : Component { T _field; }"
        transform c "new C<string>()" =? []
        transform c "new C<Component>()" =? []

    [<Test; Ignore("not yet implemented")>]
    let ``inherited component with non-conflicting field names`` () =
        let c = "class C : Component { int _field; } class D : C { bool _otherField; }"
        transform c "new D()" =? [ Field ("_field", IntType); Field ("_otherField", BoolType) ]

    [<Test; Ignore("not yet implemented")>]
    let ``inherited component with conflicting field names`` () =
        let c = "class C : Component { int _field1; bool _field2; } class D : C { bool _field1; bool _field2; }"
        transform c "new D()" =? 
            [ 
                Field ("base._field1", IntType)
                Field ("base._field2", BoolType) 
                Field ("_field1", BoolType)
                Field ("_field2", BoolType) 
            ]