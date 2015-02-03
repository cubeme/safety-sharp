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
module ``Ssm Validation: Unbound required port`` =

    let private transform csharpCode =
        let model = TestCompilation.CreateModel csharpCode
        model.FinalizeMetadata ()
        (model, CilToSsm.transformModel model |> SsmLowering.lower)

    let private check componentNames portNames csharpCode =
        let (model, loweredSsm) = transform csharpCode
        let e = raisesWith<UnboundRequiredPortsException> (fun () -> SsmValidation.validate model loweredSsm)
        e.UnboundPorts |> List.ofArray |> List.map (fun p -> (p.Component :?> Component).UnmangledName) =? componentNames
        e.UnboundPorts |> List.ofArray |> List.map (fun p -> p.Method.Name) =? portNames

    [<Test>]
    let ``valid when all ports are bound`` () =
        let (model, loweredSsm) = 
            transform
              "class X : Component { extern void M(); void N() {} public X() { BindDelayed(RequiredPorts.M = ProvidedPorts.N); } }
               class TestModel : Model { public TestModel() { SetRootComponents(new X()); } }"

        nothrow (fun () -> SsmValidation.validate model loweredSsm)

    [<Test>]
    let ``invalid when single port is unbound`` () =
        check ["Root"] ["M"] 
          "class X : Component { extern void M(); }
           class TestModel : Model { public TestModel() { SetRootComponents(new X()); } }"

    [<Test>]
    let ``invalid when subcomponent port is unbound`` () =
        check ["Root.x"] ["N"] 
          "class X : Component { public extern void M(); public extern void N(); }
           class Y : Component { void N() {} X x = new X(); public Y() { BindInstantaneous(x.RequiredPorts.M = ProvidedPorts.N); } }
           class TestModel : Model { public TestModel() { SetRootComponents(new Y()); } }"

[<TestFixture>]
module ``Ssm Validation: Ambiguous required port bindings`` =

    let private transform csharpCode =
        let model = TestCompilation.CreateModel csharpCode
        model.FinalizeMetadata ()
        (model, CilToSsm.transformModel model |> SsmLowering.lower)

    let private check bindings kinds binders csharpCode =
        let (model, loweredSsm) = transform csharpCode
        let e = raisesWith<AmbiguousRequiredPortBindingsException> (fun () -> SsmValidation.validate model loweredSsm)
        e.AmbiguousBindings |> List.ofArray |> List.map (fun p -> 
            p |> List.ofArray |> List.map (fun b -> 
                ((b.TargetPort.Component :?> Component).UnmangledName,
                 b.TargetPort.Method.Name,
                 (b.SourcePort.Component :?> Component).UnmangledName,
                 b.SourcePort.Method.Name)
            )
        ) =? bindings
        let bindings = e.AmbiguousBindings |> Array.collect id
        bindings |> List.ofArray |> List.map (fun binding -> binding.Kind) =? kinds
        bindings |> List.ofArray |> List.map (fun binding -> (binding.Component :?> Component).UnmangledName) =? binders

    [<Test>]
    let ``valid when all ports are bound`` () =
        let (model, loweredSsm) = 
            transform
              "class X : Component { extern void M(); void N() {} public X() { BindDelayed(RequiredPorts.M = ProvidedPorts.N); } }
               class TestModel : Model { public TestModel() { SetRootComponents(new X()); } }"

        nothrow (fun () -> SsmValidation.validate model loweredSsm)

    [<Test>]
    let ``invalid when single port is bound ambiguously by the same component`` () =
        check [[("Root", "M", "Root", "N"); ("Root", "M", "Root", "R")]] [Delayed; Delayed] ["Root"; "Root"]
          "class X : Component { extern void M(); void N() {} void R() {} public X() { BindDelayed(RequiredPorts.M = ProvidedPorts.N); BindDelayed(RequiredPorts.M = ProvidedPorts.R); } }
           class TestModel : Model { public TestModel() { SetRootComponents(new X()); } }"

    [<Test>]
    let ``invalid when single port is bound ambiguously by different components`` () =
        check [["Root.x", "M", "Root", "N"; "Root.x", "M", "Root.x", "N"]] [Instantaneous; Delayed] ["Root"; "Root.x"]
          "class X : Component { public extern void M(); void N() {} public X() { BindDelayed(RequiredPorts.M = ProvidedPorts.N); } }
           class Y : Component { X x = new X(); void N() {} public Y() { BindInstantaneous(x.RequiredPorts.M = ProvidedPorts.N); } }
           class TestModel : Model { public TestModel() { SetRootComponents(new Y()); } }"

    [<Test>]
    let ``invalid when multiple ports are bound ambiguously`` () =
        check [[("Root", "N", "Root", "A"); ("Root", "N", "Root", "B")]; [("Root", "M", "Root", "A"); ("Root", "M", "Root", "B")]] 
          [Delayed; Instantaneous; Delayed; Instantaneous] ["Root"; "Root"; "Root"; "Root"]
          "class X : Component { 
                extern void N();
                extern void M();
                void A() {}
                void B() {}
                public X() {
                    BindDelayed(RequiredPorts.N = ProvidedPorts.A);
                    BindInstantaneous(RequiredPorts.N = ProvidedPorts.B);
                    BindDelayed(RequiredPorts.M = ProvidedPorts.A);
                    BindInstantaneous(RequiredPorts.M = ProvidedPorts.B);
                }
           }
           class TestModel : Model { public TestModel() { SetRootComponents(new X()); } }"

//[<TestFixture>]
//module ``Ssm Validation: Cyclic component graph`` =
//    let private check componentNames portNames csharpCode =
//        let model = TestCompilation.CreateModel csharpCode
//        model.FinalizeMetadata ()
//        
//        let e = raisesWith<UnboundRequiredPortsException> (fun () -> model.CheckForInstantaneousCycles ())
//        e.UnboundPorts.Length =? List.length componentNames
//        e.UnboundPorts |> List.ofArray |> List.map (fun p -> p.Component.UnmangledName) =? componentNames
//        e.UnboundPorts |> List.ofArray |> List.map (fun p -> p.Port.Name) =? portNames
//
//    [<Test>]
//    let ``throws when metadata has not yet been finalized`` () =
//        let model = EmptyModel ()
//        raisesInvalidOpException (fun () -> model.CheckForInstantaneousCycles ())
//
//    [<Test>]
//    let ``does not throw for model without any cycles`` () =
//        check ["Root"] ["M"] 
//          "class X : Component { 
//                extern void M(); 
//                void N() { }
//                public override void Update() { M(); } 
//                public X() { BindInstantaneous(RequiredPorts.M = ProvidedPorts.N); }
//           }
//           class TestModel : Model { public TestModel() { SetRootComponents(new X()); } }"
