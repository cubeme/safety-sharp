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
    type ComponentWithoutValidFields =
        inherit Component

        new () = { c = null; s = null }

        val private c : Component
        val private s : string

    let private transform comp = 
        let model = TestModel comp
        model.FinalizeMetadata ()
        let ssm = CilToSsm.transformModel model
        ssm.Fields

    let private arg name t = Arg (name, t)
    let private local name t = Local (name, t)
    let private tmp = CilToSsm.freshLocal

    [<Test>]
    let ``component without fields`` () =
        transform [| EmptyComponent () |] =? []

    [<Test>]
    let ``component without fields; fields with unsupported types are ignored`` () =
        transform [| ComponentWithoutValidFields () |] =? []

    [<Test>]
    let ``component with single field`` () =
        transform [| OneFieldComponent () |] =? [ Field (fsharpFieldName "_field", IntType) ]

    [<Test>]
    let ``component with two fields`` () =
        transform [| TwoFieldsComponent () |] =? [ Field (fsharpFieldName "_field1", IntType); Field (fsharpFieldName "_field2", BoolType) ]

    [<Test; Ignore("not yet implemented")>]
    let ``generic component with generic field of supported type`` () =
        transform [| GenericComponent<int> () |] =? [ Field (fsharpFieldName "_field", IntType) ]
        transform [| GenericComponent<bool> () |] =? [ Field (fsharpFieldName "_field", BoolType) ]

    [<Test>]
    let ``generic component with generic field of unsupported type`` () =
        transform [| GenericComponent<Component> () |] =? []
        transform [| GenericComponent<string> () |] =? []