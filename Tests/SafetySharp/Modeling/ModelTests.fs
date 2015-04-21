﻿// The MIT License (MIT)
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

namespace Modeling.``Model Tests``

open System
open System.Linq
open System.Linq.Expressions
open System.Reflection
open NUnit.Framework
open SafetySharp.Modeling
open Modeling

[<TestFixture>]
module ``FinalizeMetadata method`` =
    [<Test>]
    let ``throws when the metadata has already been finalized`` () =
        let model = TestModel (EmptyComponent ())
        model.FinalizeMetadata ()

        raisesInvalidOpException (fun () -> model.FinalizeMetadata () |> ignore)

    [<Test>]
    let ``throws when no root has been set`` () =
        let model = EmptyModel ()
        raisesInvalidOpException (fun () -> model.FinalizeMetadata () |> ignore)

    [<Test>]
    let ``updates the IsMetadataFinalized property`` () =
        let model = TestModel (EmptyComponent ())
        model.IsMetadataFinalized =? false

        model.FinalizeMetadata ()
        model.IsMetadataFinalized =? true

[<TestFixture>]
module ``SetRootComponents method`` =
    let raisesSharedComponentsException func components =
        let e = raisesWith<SharedComponentsException> func 
        e.Components =? components

    [<Test>]
    let ``throws when null is passed`` () =
        raisesArgumentNullException "rootComponents" (fun () -> TestModel null |> ignore)

    [<Test>]
    let ``throws when empty component array is passed`` () =
        raisesArgumentException "rootComponents" (fun () -> TestModel [||] |> ignore)

    [<Test>]
    let ``throws when the metadata has already been finalized`` () =
        let model = TestModel (EmptyComponent ())
        model.FinalizeMetadata ()

        raisesInvalidOpException (fun () -> model.SetRootComponents [| EmptyComponent () :> Component |] |> ignore)

    [<Test>]
    let ``throws when root components have been passed via the constructor`` () =
        let model = Model (EmptyComponent ())
        raisesInvalidOpException (fun () -> model.SetRootComponents [| EmptyComponent () :> Component |] |> ignore)

    [<Test>]
    let ``throws when method is called twice on same object`` () =
        let model = EmptyModel ()
        model.SetRootComponents [| EmptyComponent () :> Component |]

        raisesInvalidOpException (fun () -> model.SetRootComponents [| EmptyComponent () :> Component |] |> ignore)

    [<Test>]
    let ``throws when component is shared within the same root at the same level`` () =
        let component1 = EmptyComponent ()
        raisesSharedComponentsException (fun () -> TestModel (component1, component1) |> ignore) [|component1|]

    [<Test>]
    let ``throws when component is shared within the same root at different levels`` () =
        let component1 = EmptyComponent ()
        let component2 = EmptyComponent ()
        let component3 = OneSubcomponent component2
        let component4 = ComplexComponent (component1, component3, obj ())
        let component5 = ComplexComponent (component4, component2, obj ())

        raisesSharedComponentsException (fun () -> TestModel component5 |> ignore) [|component2|]

    [<Test>]
    let ``throws when component is shared between different roots at different levels`` () =
        let component1 = EmptyComponent ()
        let component2 = EmptyComponent ()
        let component3 = OneSubcomponent component2
        let component4 = ComplexComponent (component1, component3, obj ())
        let component5 = EmptyComponent ()
        let component6 = ComplexComponent (component5, component2, obj ())

        raisesSharedComponentsException (fun () -> TestModel (component4, component6) |> ignore) [|component2|]

    [<Test>]
    let ``throws when multiple components are shared between different roots at different levels`` () =
        let component1 = EmptyComponent ()
        let component2 = EmptyComponent ()
        let component3 = OneSubcomponent component2
        let component4 = ComplexComponent (component1, component3, obj ())
        let component5 = ComplexComponent (component1, component2, obj ())

        raisesSharedComponentsException (fun () -> TestModel (component4, component5) |> ignore) [|component1; component2|]

    [<Test>]
    let ``throws for cyclic component graph instead of stack overflowing`` () =
        let component' = SelfSubcomponent ()
        raisesSharedComponentsException (fun () -> TestModel (component') |> ignore) [|component'|]

[<TestFixture>]
module ``Components property`` =
    [<Test>]
    let ``throws when metadata has not yet been finalized`` () =
        let model = TestModel (EmptyComponent ())
        raisesInvalidOpException (fun () -> model.Components |> ignore)

    [<Test>]
    let ``does not contain non-component null-objects`` () =
        let component1 = EmptyComponent ()
        let component2 = EmptyComponent ()
        let component3 = ComplexComponent (component1, component2, null)
        let model = TestModel component3
        model.FinalizeMetadata ()

        model.Components =? [component3; component1; component2]

    [<Test>]
    let ``does not contain non-component objects`` () =
        let component1 = EmptyComponent ()
        let component2 = EmptyComponent ()
        let component3 = ComplexComponent (component1, component2, obj ())
        let model = TestModel component3
        model.FinalizeMetadata ()

        model.Components =? [component3; component1; component2]

    [<Test>]
    let ``does not contain null-components`` () =
        let component' = OneSubcomponent ()
        let model = TestModel component'
        model.FinalizeMetadata ()

        model.Components =? [component']

    [<Test>]
    let ``contains roots`` () =
        let component1 = EmptyComponent ()
        let component2 = EmptyComponent ()
        let model = TestModel (component1, component2)
        model.FinalizeMetadata ()

        model.Components =? [component1; component2]

    [<Test>]
    let ``contains all components of linear hierarchy with two levels`` () =
        let component1 = EmptyComponent ()
        let component2 = OneSubcomponent component1
        let model = TestModel component2
        model.FinalizeMetadata ()

        model.Components =? [component2; component1]

    [<Test>]
    let ``contains all components of linear hierarchy with four levels`` () =
        let component1 = EmptyComponent ()
        let component2 = OneSubcomponent component1
        let component3 = OneSubcomponent component2
        let component4 = OneSubcomponent component3
        let model = TestModel component4
        model.FinalizeMetadata ()

        model.Components =? [component4; component3; component2; component1]

    [<Test>]
    let ``contains all components of complex hierarchy`` () =
        let component1 = EmptyComponent ()
        let component2 = EmptyComponent ()
        let component3 = OneSubcomponent component2
        let component4 = ComplexComponent (component1, component3, obj ())
        let component5 = EmptyComponent ()
        let component6 = ComplexComponent(component4, component5, obj ())
        let model = TestModel component6
        model.FinalizeMetadata ()

        model.Components =? [component6; component4; component1; component3; component2; component5]

    [<Test>]
    let ``all contained components have finalized metadata`` () =
        let component1 = EmptyComponent ()
        let component2 = EmptyComponent ()
        let component3 = EmptyComponent ()
        let component4 = OneSubcomponent component1
        let component5 = TwoSubcomponents (component2, component3)
        let model = TestModel (component4, component5)
        model.FinalizeMetadata ()

        model.Components |> List.iter (fun component' -> component'.IsMetadataFinalized =? true)

    [<Test>]
    let ``all contained components have their tree path and subcomponent index encoded in their name`` () =
        let component1 = EmptyComponent ()
        let component2 = EmptyComponent ()
        let component3 = EmptyComponent ()
        let component4 = OneSubcomponent component1
        let component5 = OneSubcomponent component3
        let component6 = TwoSubcomponents (component2, component5)
        let model = TestModel (component4, component6)
        model.FinalizeMetadata ()

        let name root = function
            | [] -> sprintf "SynRoot.Root%i@%i" root root
            | fields -> sprintf "SynRoot.Root%i@%i.%s" root root <| String.Join (".", fields |> List.map (fun (name, idx) -> fsharpSubcomponentName name idx))
        
        model.Components |> List.map (fun component' -> component'.Name) =?
        [name 0 []; name 0 [("_component", 0)]; name 1 []; name 1 [("_component1", 0)]; name 1 [("_component2", 1)]; name 1 [("_component2", 1); ("_component", 0)]] 

[<TestFixture>]
module ``Roots property`` =
    [<Test>]
    let ``throws when metadata has not yet been finalized`` () =
        let model = TestModel (EmptyComponent ())
        raisesInvalidOpException (fun () -> model.Roots |> ignore)

    [<Test>]
    let ``contains single top-level component`` () =
        let component' = EmptyComponent ()
        let model = TestModel (component')
        model.FinalizeMetadata ()

        model.Roots =? [component']

    [<Test>]
    let ``contains multiple top-level components`` () =
        let component1 = EmptyComponent ()
        let component2 = EmptyComponent ()
        let component3 = EmptyComponent ()
        let model = TestModel (component1, component2, component3)
        model.FinalizeMetadata ()

        model.Roots =? [component1; component2; component3]

    [<Test>]
    let ``does not contain nested components`` () =
        let component1 = EmptyComponent ()
        let component2 = OneSubcomponent component1
        let model = TestModel component2
        model.FinalizeMetadata ()

        model.Roots =? [component2]

    [<Test>]
    let ``contained roots have unique names`` () =
        let model = TestModel (EmptyComponent ())
        model.FinalizeMetadata ()
        model.Roots.[0].Name =? "SynRoot.Root0@0"

        let model = TestModel (EmptyComponent (), EmptyComponent (), EmptyComponent ())
        model.FinalizeMetadata ()
        model.Roots.[0].Name =? "SynRoot.Root0@0"
        model.Roots.[1].Name =? "SynRoot.Root1@1"
        model.Roots.[2].Name =? "SynRoot.Root2@2"

[<TestFixture>]
module ``Bind method`` =
    let mutable component' = (null :> Component)

    let private bindings csharpCode initialization rootNames =
        let csharpCode = sprintf "class TestModel : Model { public TestModel() { %s SetRootComponents(%s); } } %s" initialization rootNames csharpCode
        let model = TestCompilation.CreateModel csharpCode
        model.FinalizeMetadata ()
        component' <- model.SynthesizedRoot

    [<Test>]
    let ``throws when null is passed`` () =
        let model = TestModel (EmptyComponent ())
        raisesArgumentNullException "binding" (fun () -> model.Bind null |> ignore)

    [<Test>]
    let ``throws when metadata has already been finalized`` () =
        let model = TestModel (EmptyComponent ())
        model.FinalizeMetadata ()
        raisesInvalidOpException (fun () -> model.Bind (PortBinding (PortInfo (null, null), PortInfo(null, null))) |> ignore)

    [<Test>]
    let ``returns empty list for model without bindings`` () =
        bindings "class X : Component { void M() {} extern void N(); }" "" "new X()"
        component'.Bindings =? []

    [<Test>]
    let ``returns delayed port binding of a component`` () =
        bindings "class X : Component { public void M() {} public extern void N(); }" "var x = new X(); Bind(x.RequiredPorts.N = x.ProvidedPorts.M).Delayed();" "x"
        component'.Bindings.Length =? 1
        component'.Bindings.[0].Kind =? BindingKind.Delayed
        component'.Bindings.[0].TargetPort.IsRequiredPort =? true
        component'.Bindings.[0].TargetPort.Component =? (component'.Subcomponents.[0] :> obj)
        component'.Bindings.[0].TargetPort.Method.Name =? "N"
        component'.Bindings.[0].SourcePort.IsRequiredPort =? false
        component'.Bindings.[0].SourcePort.Component =? (component'.Subcomponents.[0] :> obj)
        component'.Bindings.[0].SourcePort.Method.Name =? "M"

    [<Test>]
    let ``returns instantaneous port binding of a component`` () =
        bindings "class X : Component { public void M() {} public extern void N(); }" "var x = new X(); Bind(x.RequiredPorts.N = x.ProvidedPorts.M);" "x"
        component'.Bindings.Length =? 1
        component'.Bindings.[0].Kind =? BindingKind.Instantaneous
        component'.Bindings.[0].TargetPort.IsRequiredPort =? true
        component'.Bindings.[0].TargetPort.Component =? (component'.Subcomponents.[0] :> obj)
        component'.Bindings.[0].TargetPort.Method.Name =? "N"
        component'.Bindings.[0].SourcePort.IsRequiredPort =? false
        component'.Bindings.[0].SourcePort.Component =? (component'.Subcomponents.[0] :> obj)
        component'.Bindings.[0].SourcePort.Method.Name =? "M"

    [<Test>]
    let ``returns multiple port binding between subcomponents`` () =
        bindings "class Y : Component { public void M() {} public extern void N(); } class X : Component { public Y y1 = new Y(); public Y y2 = new Y(); }" "var x = new X(); Bind(x.y1.RequiredPorts.N = x.y2.ProvidedPorts.M); Bind(x.y2.RequiredPorts.N = x.y1.ProvidedPorts.M).Delayed();" "x"
        component'.Bindings.Length =? 2
        component'.Bindings.[0].Kind =? BindingKind.Instantaneous
        component'.Bindings.[0].TargetPort.IsRequiredPort =? true
        component'.Bindings.[0].TargetPort.Component =? (component'.Subcomponents.[0].Subcomponents.[0] :> obj)
        component'.Bindings.[0].TargetPort.Method.Name =? "N"
        component'.Bindings.[0].SourcePort.IsRequiredPort =? false
        component'.Bindings.[0].SourcePort.Component =? (component'.Subcomponents.[0].Subcomponents.[1] :> obj)
        component'.Bindings.[0].SourcePort.Method.Name =? "M"
        component'.Bindings.[1].Kind =? BindingKind.Delayed
        component'.Bindings.[1].TargetPort.IsRequiredPort =? true
        component'.Bindings.[1].TargetPort.Component =? (component'.Subcomponents.[0].Subcomponents.[1] :> obj)
        component'.Bindings.[1].TargetPort.Method.Name =? "N"
        component'.Bindings.[1].SourcePort.IsRequiredPort =? false
        component'.Bindings.[1].SourcePort.Component =? (component'.Subcomponents.[0].Subcomponents.[0] :> obj)
        component'.Bindings.[1].SourcePort.Method.Name =? "M"