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

namespace Modeling.Binding

open System
open System.Linq
open System.Linq.Expressions
open System.Reflection
open NUnit.Framework
open SafetySharp.Runtime.Modeling
open Modeling

[<TestFixture>]
module ``Instantaneous Bindings`` =

    let getFieldValue<'a> obj fieldName =
        obj.GetType().GetField(fieldName).GetValue(obj) :?> 'a

    let invoke obj methodName args =
        obj.GetType().GetMethod(methodName).Invoke (obj, args)

    [<Test>]
    let ``model binding of 'void -> void' port`` () =
        let model = TestCompilation.CreateModel "
            class X : Component {
                public extern void Req();
                public void Prov() { i = 17; }
                public int i;
            }
            class TestModel : Model {
                public TestModel() { var x = new X(); SetRootComponents(x); Bind(x.RequiredPorts.Req = x.ProvidedPorts.Prov); }
            }
        "
        model.FinalizeMetadata ()

        getFieldValue<int> model.Roots.[0] "i" =? 0
        invoke model.Roots.[0] "Req" null |> ignore
        getFieldValue<int> model.Roots.[0] "i" =? 17

    [<Test>]
    let ``model binding of 'int -> int' port`` () =
        let model = TestCompilation.CreateModel "
            class X : Component {
                public extern int Req(int i);
                public int Prov(int i) { return i; }
            }
            class TestModel : Model {
                public TestModel() { var x = new X(); SetRootComponents(x); Bind(x.RequiredPorts.Req = x.ProvidedPorts.Prov); }
            }
        "
        model.FinalizeMetadata ()

        invoke model.Roots.[0] "Req" [|4 :> obj|] :?> int =? 4

    [<Test>]
    let ``model binding between different components`` () =
        let model = TestCompilation.CreateModel "
            class X : Component {
                public int Prov(int i) { return i; }
            }
            class Y : Component {
                public extern int Req(int i);
            }
            class TestModel : Model {
                public TestModel() { 
                    var x = new X(); 
                    var y = new Y(); 
                    SetRootComponents(x, y); 
                    Bind(y.RequiredPorts.Req = x.ProvidedPorts.Prov); 
                }
            }
        "
        model.FinalizeMetadata ()

        invoke model.Roots.[1] "Req" [|4 :> obj|] :?> int =? 4

    [<Test>]
    let ``component binding of 'void -> void' port`` () =
        let model = TestCompilation.CreateModel "
            class X : Component {
                public extern void Req();
                public void Prov() { i = 17; }
                public int i;
                public X() { Bind(RequiredPorts.Req = ProvidedPorts.Prov); }
            }
            class TestModel : Model {
                public TestModel() { var x = new X(); SetRootComponents(x); }
            }
        "
        model.FinalizeMetadata ()

        getFieldValue<int> model.Roots.[0] "i" =? 0
        invoke model.Roots.[0] "Req" null |> ignore
        getFieldValue<int> model.Roots.[0] "i" =? 17

    [<Test>]
    let ``component binding of 'int -> int' port`` () =
        let model = TestCompilation.CreateModel "
            class X : Component {
                public extern int Req(int i);
                public int Prov(int i) { return i; }
                public X() { Bind(RequiredPorts.Req = ProvidedPorts.Prov); }
            }
            class TestModel : Model {
                public TestModel() { var x = new X(); SetRootComponents(x); }
            }
        "
        model.FinalizeMetadata ()

        invoke model.Roots.[0] "Req" [|4 :> obj|] :?> int =? 4

    [<Test>]
    let ``component binding replacement`` () =
        let model = TestCompilation.CreateModel "
            class X : Component {
                public extern int Req(int i);
                public int Prov(int i) { return i; }
                public X() { Bind(RequiredPorts.Req = ProvidedPorts.Prov); }
            }
            class Y : X { 
                public new int Prov(int i) { return i * 2; }
                public Y() { Bind(RequiredPorts.Req = ProvidedPorts.Prov); }
            }
            class TestModel : Model {
                public TestModel() { var x = new Y(); SetRootComponents(x); }
            }
        "
        model.FinalizeMetadata ()

        invoke model.Roots.[0] "Req" [|4 :> obj|] :?> int =? 8

    [<Test>]
    let ``component binding of inherited ports`` () =
        let model = TestCompilation.CreateModel "
            class X : Component {
                public extern int Req(int i);
                public int Prov(int i) { return i; }
                public X() { Bind(RequiredPorts.Req = ProvidedPorts.Prov); }
            }
            class Y : X { 
                public Y() { Bind(RequiredPorts.Req = ProvidedPorts.Prov); }
            }
            class TestModel : Model {
                public TestModel() { var x = new Y(); SetRootComponents(x); }
            }
        "
        model.FinalizeMetadata ()

        invoke model.Roots.[0] "Req" [|4 :> obj|] :?> int =? 4

    [<Test>]
    let ``virtual component binding`` () =
        let model = TestCompilation.CreateModel "
            class X : Component {
                public extern int Req(int i);
                public virtual int Prov(int i) { return i; }
                public X() { Bind(RequiredPorts.Req = ProvidedPorts.Prov); }
            }
            class Y : X { 
                public override int Prov(int i) { return i * 3; }
            }
            class TestModel : Model {
                public TestModel() { var x = new Y(); SetRootComponents(x); }
            }
        "
        model.FinalizeMetadata ()

        invoke model.Roots.[0] "Req" [|4 :> obj|] :?> int =? 12