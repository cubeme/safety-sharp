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

namespace SafetySharp.Tests.CSharp.Transformation.ObjectTransformationTests

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Internal.CSharp
open SafetySharp.Internal.Metamodel
open SafetySharp.Modeling
open SafetySharp.Tests.CSharp
open SafetySharp.Tests
open SafetySharp.Internal.CSharp.Transformation

[<AutoOpen>]
module private ObjectTransformationTestsHelper =
    let mutable symbolResolver = Unchecked.defaultof<SymbolResolver>
    let mutable objectResolver = Unchecked.defaultof<ObjectResolver>
    let mutable components = Unchecked.defaultof<Component list>
    let mutable modelObject = Unchecked.defaultof<ModelObject>
    let mutable modelSymbol = Unchecked.defaultof<ModelSymbol>
    let mutable model : Model = null

    let compile csharpCode componentTypes =
        let compilation = TestCompilation csharpCode

        components <- componentTypes |> List.map compilation.CreateObject
        model <- TestModel (components |> Array.ofList)
        model.FinalizeMetadata ()

        symbolResolver <- SymbolTransformation.Transform compilation.CSharpCompilation model
        objectResolver <- ObjectTransformation.Transform model symbolResolver
        modelSymbol <- symbolResolver.ModelSymbol
        modelObject <- objectResolver.ModelObject

    let createPartition (rootComponent : Component) = {
        RootComponent = objectResolver.ResolveObject rootComponent
        PartitionSymbol = { Name = rootComponent.Name; RootComponent = symbolResolver.ResolveComponent rootComponent }
    }

[<TestFixture>]
module ``Transform method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        let compilation = TestCompilation "class A : Component {}"
        let symbolResolver = SymbolTransformation.TransformComponentSymbols compilation.CSharpCompilation
        raisesArgumentNullException "model" (fun () -> ObjectTransformation.Transform null symbolResolver |> ignore)

    [<Test>]
    let ``throws when model metadata has not yet been finalized`` () =
        let compilation = TestCompilation "class A : Component {}"
        symbolResolver <- SymbolTransformation.TransformComponentSymbols compilation.CSharpCompilation
        let model = TestModel (EmptyComponent ())

        raisesArgumentException "model" (fun () -> ObjectTransformation.Transform model symbolResolver |> ignore)

[<TestFixture>]
module ``ModelObject property`` =
    [<Test>]
    let ``contains one root partition`` () =
        compile "class A : Component {}" ["A"]
        modelObject.Partitions =? [createPartition components.[0]]

    [<Test>]
    let ``contains three root partitions`` () =
        compile "class A : Component {} class B : A {}" ["A"; "B"; "A"]
        modelObject.Partitions =? [
            createPartition components.[0]
            createPartition components.[1]
            createPartition components.[2]
        ]

    [<Test>]
    let ``component has correct initial field values`` () =
        compile "class A : Component { public A() { SetInitialValues(() => x, 1, 2, 3); } int x; decimal d = 77.7m; }" ["A"]
        let componentSymbol = symbolResolver.ResolveComponent components.[0]
        let fieldSymbol1 = componentSymbol.Fields.[0]
        let fieldSymbol2 = componentSymbol.Fields.[1]

        modelObject.Partitions.[0].RootComponent =? { 
            emptyComponentObject "Root0" componentSymbol with
                Fields = 
                [
                    fieldSymbol1, { FieldSymbol = fieldSymbol1; InitialValues = [1; 2; 3] }
                    fieldSymbol2, { FieldSymbol = fieldSymbol2; InitialValues = [77.7m] }
                ] |> Map.ofList
        }

    [<Test>]
    let ``component has correct subcomponents`` () =
        compile "class A : Component { B b1 = new B(); B b2 = new B(); } class B : Component {}" ["A"; "B"]
        let componentSymbolA = symbolResolver.ResolveComponent components.[0]
        let componentSymbolB = symbolResolver.ResolveComponent components.[1]
        let subcomponentSymbol1 = symbolResolver.ModelSymbol.Subcomponents.[componentSymbolA].[0]
        let subcomponentSymbol2 = symbolResolver.ModelSymbol.Subcomponents.[componentSymbolA].[1]

        modelObject.Partitions.[0].RootComponent =? { 
            emptyComponentObject "Root0" componentSymbolA with
                Subcomponents = 
                [
                    subcomponentSymbol1, emptyComponentObject "Root0.b1" componentSymbolB
                    subcomponentSymbol2, emptyComponentObject "Root0.b2" componentSymbolB
                ] |> Map.ofList
        }

    [<Test>]
    let ``model maps root component objects`` () =
        compile "class A : Component {} class B : Component {}" ["A"; "B"]
        modelObject.ComponentObjects =? Map.ofList [
            modelSymbol.ComponentObjects.[0], emptyComponentObject "Root0" (symbolResolver.ResolveComponent components.[0])
            modelSymbol.ComponentObjects.[1], emptyComponentObject "Root1" (symbolResolver.ResolveComponent components.[1])
        ]

    [<Test>]
    let ``model maps root and nested component objects`` () =
        compile "class A : Component { B b1 = new B(); B b2 = new B(); } class B : Component {}" ["A"; "B"]
        let componentSymbolA = symbolResolver.ResolveComponent components.[0]
        let componentSymbolB = symbolResolver.ResolveComponent components.[1]
        let subcomponentSymbol1 = symbolResolver.ModelSymbol.Subcomponents.[componentSymbolA].[0]
        let subcomponentSymbol2 = symbolResolver.ModelSymbol.Subcomponents.[componentSymbolA].[1]
        let nestedComponent = {
            emptyComponentObject "Root0" componentSymbolA with
                Subcomponents =
                [
                    subcomponentSymbol1, emptyComponentObject "Root0.b1" componentSymbolB
                    subcomponentSymbol2, emptyComponentObject "Root0.b2" componentSymbolB
                ] |> Map.ofList
        }
        modelObject.ComponentObjects =? Map.ofList [
            modelSymbol.ComponentObjects.[0], nestedComponent
            modelSymbol.ComponentObjects.[1], emptyComponentObject "Root0.b1" componentSymbolB
            modelSymbol.ComponentObjects.[2], emptyComponentObject "Root0.b2" componentSymbolB
            modelSymbol.ComponentObjects.[3], emptyComponentObject "Root1" componentSymbolB
        ]

    [<Test>]
    let ``reflects three-level nested hierarchy with multiple roots`` () =
        compile "
            class A : Component {
                B b1 = new B();
                B b2 = new B();
            }
            class B : Component {
                C c = new C();
            }
            class C : Component {
            }" ["A"; "B"; "C"]

        let componentSymbolA = symbolResolver.ResolveComponent components.[0]
        let componentSymbolB = symbolResolver.ResolveComponent components.[1]
        let componentSymbolC = symbolResolver.ResolveComponent components.[2]
        let subcomponentSymbol1 = symbolResolver.ModelSymbol.Subcomponents.[componentSymbolA].[0]
        let subcomponentSymbol2 = symbolResolver.ModelSymbol.Subcomponents.[componentSymbolA].[1]
        let subcomponentSymbol3 = symbolResolver.ModelSymbol.Subcomponents.[componentSymbolB].[0]

        let partition0 = { 
            emptyComponentObject "Root0" componentSymbolA with
                Subcomponents =
                [
                    subcomponentSymbol1, { 
                        emptyComponentObject "Root0.b1" componentSymbolB with
                            Subcomponents = [subcomponentSymbol3, emptyComponentObject "Root0.b1.c" componentSymbolC] |> Map.ofList
                    }
                    subcomponentSymbol2, {
                        emptyComponentObject "Root0.b2" componentSymbolB with
                            Subcomponents = [subcomponentSymbol3, emptyComponentObject "Root0.b2.c" componentSymbolC] |> Map.ofList
                    } 
                ] |> Map.ofList
        }

        let partition1 = {
            emptyComponentObject "Root1" componentSymbolB with
                Subcomponents = [subcomponentSymbol3, emptyComponentObject "Root1.c" componentSymbolC] |> Map.ofList
        }

        let partition2 = emptyComponentObject "Root2" componentSymbolC

        modelObject.Partitions =? 
        [
            { PartitionSymbol = symbolResolver.ResolvePartition components.[0]; RootComponent = partition0 }
            { PartitionSymbol = symbolResolver.ResolvePartition components.[1]; RootComponent = partition1 }
            { PartitionSymbol = symbolResolver.ResolvePartition components.[2]; RootComponent = partition2 }
        ]

[<TestFixture>]
module ``ResolveSymbol Method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        compile "class A : Component {}" ["A"]
        raisesArgumentNullException "componentObject" (fun () -> objectResolver.ResolveSymbol null |> ignore)

    [<Test>]
    let ``throws when component of unknown type is passed`` () =
        compile "class A : Component {}" ["A"]
        raisesArgumentException "componentObject" (fun () -> objectResolver.ResolveSymbol (EmptyComponent ()) |> ignore)

    [<Test>]
    let ``returns component symbol for component object of known type`` () =
        compile "class A : Component {}" ["A"]
        objectResolver.ResolveSymbol components.[0] =? symbolResolver.ComponentSymbols.[0]

    [<Test>]
    let ``returns different component symbols for different component objects of different known types`` () =
        compile "class A : Component {} class B : Component {}" ["A"; "B"]
        objectResolver.ResolveSymbol components.[0] =? symbolResolver.ComponentSymbols.[0]
        objectResolver.ResolveSymbol components.[1] =? symbolResolver.ComponentSymbols.[1]
        objectResolver.ResolveSymbol components.[0] <>? objectResolver.ResolveSymbol components.[1]

    [<Test>]
    let ``returns same component symbols for different component objects of same known type`` () =
        compile "class A : Component {}" ["A"; "A"]
        objectResolver.ResolveSymbol components.[0] =? symbolResolver.ComponentSymbols.[0]
        objectResolver.ResolveSymbol components.[1] =? symbolResolver.ComponentSymbols.[0]

        // We have to check for reference equality here
        obj.ReferenceEquals (objectResolver.ResolveSymbol components.[0], objectResolver.ResolveSymbol components.[1]) =? true

[<TestFixture>]
module ``ResolveObject Method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        compile "class A : Component {}" ["A"]
        raisesArgumentNullException "componentObject" (fun () -> objectResolver.ResolveObject null |> ignore)

    [<Test>]
    let ``throws when component of unknown type is passed`` () =
        compile "class A : Component {}" ["A"]
        raisesArgumentException "componentObject" (fun () -> objectResolver.ResolveObject (EmptyComponent ()) |> ignore)

    [<Test>]
    let ``returns component object for component object of known type`` () =
        compile "class A : Component {}" ["A"]
        objectResolver.ResolveObject components.[0] =? emptyComponentObject "Root0" symbolResolver.ComponentSymbols.[0]

    [<Test>]
    let ``returns different component symbols for different component objects of different known types`` () =
        compile "class A : Component {} class B : Component {}" ["A"; "B"]
        objectResolver.ResolveObject components.[0] =? emptyComponentObject "Root0" symbolResolver.ComponentSymbols.[0]
        objectResolver.ResolveObject components.[1] =? emptyComponentObject "Root1" symbolResolver.ComponentSymbols.[1]
        objectResolver.ResolveObject components.[0] <>? objectResolver.ResolveObject components.[1]

    [<Test>]
    let ``returns different component symbols for different component objects of same known type`` () =
        compile "class A : Component {}" ["A"; "A"]
        objectResolver.ResolveObject components.[0] =? emptyComponentObject "Root0" symbolResolver.ComponentSymbols.[0]
        objectResolver.ResolveObject components.[1] =? emptyComponentObject "Root1" symbolResolver.ComponentSymbols.[0]
        objectResolver.ResolveObject components.[0] <>? objectResolver.ResolveObject components.[1]