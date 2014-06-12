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

namespace SafetySharp.Tests.Modeling.ModelTests

open System
open System.Linq
open System.Linq.Expressions
open System.Reflection
open NUnit.Framework
open Swensen.Unquote
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp
open SafetySharp.Metamodel
open SafetySharp.Modeling
open SafetySharp.Tests.CSharp
open SafetySharp.Tests.Modeling

[<TestFixture>]
module ``FinalizeMetadata method`` =
    [<Test>]
    let ``throws when the metadata has already been finalized`` () =
        let model = TestModel (EmptyComponent ())
        model.FinalizeMetadata ()

        raises<InvalidOperationException> <@ model.FinalizeMetadata () @>

    [<Test>]
    let ``throws when no partition root has been set`` () =
        let model = EmptyModel ()
        raises<InvalidOperationException> <@ model.FinalizeMetadata () @>

    [<Test>]
    let ``updates the IsMetadataFinalized property`` () =
        let model = TestModel (EmptyComponent ())
        model.IsMetadataFinalized =? false

        model.FinalizeMetadata ()
        model.IsMetadataFinalized =? true

[<TestFixture>]
module ``SetPartitionRoots method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        raisesWith<ArgumentNullException> <@ TestModel null @> (fun e -> <@ e.ParamName = "rootComponents" @>)

    [<Test>]
    let ``throws when empty component array is passed`` () =
        raisesWith<ArgumentException> <@ TestModel [||] @> (fun e -> <@ e.ParamName = "rootComponents" @>)

    [<Test>]
    let ``throws when the metadata has already been finalized`` () =
        let model = TestModel (EmptyComponent ())
        model.FinalizeMetadata ()

        raises<InvalidOperationException> <@ model.SetPartitions [| EmptyComponent () :> Component |] @>

    [<Test>]
    let ``throws when method is called twice on same object`` () =
        let model = EmptyModel ()
        model.SetPartitions [| EmptyComponent () :> Component |]

        raises<InvalidOperationException> <@ model.SetPartitions [| EmptyComponent () :> Component |] @>

    [<Test>]
    let ``throws when component is shared within the same partition root at the same level`` () =
        let component1 = EmptyComponent ()
        raisesWith<SharedComponentsException> <@ TestModel (component1, component1) @>
            (fun e -> <@ e.Components = [component1] @>)

    [<Test>]
    let ``throws when component is shared within the same partition root at different levels`` () =
        let component1 = EmptyComponent ()
        let component2 = EmptyComponent ()
        let component3 = OneSubcomponent component2
        let component4 = ComplexComponent (component1, component3, obj ())
        let component5 = ComplexComponent (component4, component2, obj ())

        raisesWith<SharedComponentsException> <@ TestModel component5 @>
            (fun e -> <@ e.Components = [component2] @>)

    [<Test>]
    let ``throws when component is shared between different roots at different levels`` () =
        let component1 =  EmptyComponent ()
        let component2 =  EmptyComponent ()
        let component3 =  OneSubcomponent component2
        let component4 =  ComplexComponent (component1, component3, obj ())
        let component5 =  EmptyComponent ()
        let component6 =  ComplexComponent (component5, component2, obj ())

        raisesWith<SharedComponentsException> <@ TestModel (component4, component6) @>
            (fun e -> <@ e.Components = [component2] @>)

    [<Test>]
    let ``throws when multiple components are shared between different roots at different levels`` () =
        let component1 =  EmptyComponent ()
        let component2 =  EmptyComponent ()
        let component3 =  OneSubcomponent component2
        let component4 =  ComplexComponent (component1, component3, obj ())
        let component5 =  ComplexComponent (component1, component2, obj ())

        raisesWith<SharedComponentsException> <@ TestModel (component4, component5) @>
            (fun e -> <@ e.Components = [component1; component2] @>)

[<TestFixture>]
module ``Components property`` =
    [<Test>]
    let ``throws when metadata has not yet been finalized`` () =
        let model = TestModel (EmptyComponent ())
        raises<InvalidOperationException> <@ model.Components @>

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
    let ``contains partition roots`` () =
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

[<TestFixture>]
module ``PartitionRoots property`` =
    [<Test>]
    let ``throws when metadata has not yet been finalized`` () =
        let model = TestModel (EmptyComponent ())
        raises<InvalidOperationException> <@ model.PartitionRoots @>

    [<Test>]
    let ``contains single top-level component`` () =
        let component' = EmptyComponent ()
        let model = TestModel (component')
        model.FinalizeMetadata ()

        model.PartitionRoots =? [component']

    [<Test>]
    let ``contains multiple top-level components`` () =
        let component1 = EmptyComponent ()
        let component2 = EmptyComponent ()
        let component3 = EmptyComponent ()
        let model = TestModel (component1, component2, component3)
        model.FinalizeMetadata ()

        model.PartitionRoots =? [component1; component2; component3]

    [<Test>]
    let ``does not contain nested components`` () =
        let component1 = EmptyComponent ()
        let component2 = OneSubcomponent component1
        let model = TestModel component2
        model.FinalizeMetadata ()

        model.PartitionRoots =? [component2]

    [<Test>]
    let ``contained partition roots have unique names`` () =
        let model = TestModel (EmptyComponent ())
        model.FinalizeMetadata ()
        model.PartitionRoots.[0].Name =? "Root0"

        let model = TestModel (EmptyComponent (), EmptyComponent (), EmptyComponent ())
        model.FinalizeMetadata ()
        model.PartitionRoots.[0].Name =? "Root0"
        model.PartitionRoots.[1].Name =? "Root1"
        model.PartitionRoots.[2].Name =? "Root2"