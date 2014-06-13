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
open Swensen.Unquote
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp
open SafetySharp.Metamodel
open SafetySharp.Modeling
open SafetySharp.Tests.CSharp
open SafetySharp.Tests
open SafetySharp.CSharp.Transformation

[<AutoOpen>]
module private ObjectTransformationTestsHelper =
    let mutable symbolResolver = Unchecked.defaultof<SymbolResolver>
    let mutable objectResolver = Unchecked.defaultof<ObjectResolver>
    let mutable components = Unchecked.defaultof<Component list>
    let mutable modelObject = Unchecked.defaultof<ModelObject>
    let mutable (model : Model) = null

    let compile csharpCode componentTypes =
        let compilation = TestCompilation csharpCode
        symbolResolver <- SymbolTransformation.Transform compilation.CSharpCompilation
        components <- componentTypes |> List.map compilation.CreateObject

        model <- TestModel (components |> Array.ofList)
        model.FinalizeMetadata ()

        objectResolver <- ObjectTransformation.Transform model symbolResolver
        modelObject <- objectResolver.ModelObject

    let createPartition rootComponent = {
        RootComponent = rootComponent
        //PartitionSymbol = (* TODO *) Unchecked.defaultof<PartitionSymbol>
    }

[<TestFixture>]
module ``Transform method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        let compilation = TestCompilation "class A : Component {}"
        let symbolResolver = SymbolTransformation.Transform compilation.CSharpCompilation
        raisesArgumentNullException "model" <@ ObjectTransformation.Transform null symbolResolver @>

    [<Test>]
    let ``throws when model metadata has not yet been finalized`` () =
        let compilation = TestCompilation "class A : Component {}"
        symbolResolver <- SymbolTransformation.Transform compilation.CSharpCompilation
        let model = TestModel (EmptyComponent ())

        raisesArgumentException "model" <@ ObjectTransformation.Transform model symbolResolver @>

[<TestFixture>]
module ``ModelObject property`` =
    [<Test>]
    let ``contains one root partition`` () =
        compile "class A : Component {}" ["A"]
        modelObject.Partitions =? [createPartition <| objectResolver.ResolveObject components.[0]]

    [<Test>]
    let ``contains three root partitions`` () =
        compile "class A : Component {} class B : A {}" ["A"; "B"; "A"]
        modelObject.Partitions =? [
            createPartition <| objectResolver.ResolveObject components.[0]
            createPartition <| objectResolver.ResolveObject components.[1]
            createPartition <| objectResolver.ResolveObject components.[2]
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
                    (fieldSymbol1, { FieldSymbol = fieldSymbol1; InitialValues = [1; 2; 3] })
                    (fieldSymbol2, { FieldSymbol = fieldSymbol2; InitialValues = [77.7m] })
                ] |> Map.ofList
        }

    [<Test>]
    let ``component has correct subcomponents`` () =
        compile "class A : Component { public A() { b1 = new B(); b2 = new B(); } B b1, b2; } class B : Component {}" ["A"; "B"]
        let componentSymbolA = symbolResolver.ResolveComponent components.[0]
        let componentSymbolB = symbolResolver.ResolveComponent components.[1]
        let subcomponentSymbol1 = symbolResolver.ModelSymbol.Subcomponents.[componentSymbolA].[0]
        let subcomponentSymbol2 = symbolResolver.ModelSymbol.Subcomponents.[componentSymbolA].[1]

        modelObject.Partitions.[0].RootComponent =? { 
            emptyComponentObject "Root0" componentSymbolA with
                Subcomponents = 
                [
                    (subcomponentSymbol1, emptyComponentObject "Root0.b1" componentSymbolB)
                    (subcomponentSymbol2, emptyComponentObject "Root0.b2" componentSymbolB)
                ] |> Map.ofList
        }

    [<Test>]
    let ``reflects three-level nested hierarchy with multiple roots`` () =
        compile "
            class A : Component {
                B b1, b2;
                public A() {
                    b1 = new B();
                    b2 = new B();
                }
            }
            class B : Component {
                C c;
                public B() {
                    c = new C();
                }
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
                    (subcomponentSymbol1, { 
                        emptyComponentObject "Root0.b1" componentSymbolB with
                            Subcomponents = [(subcomponentSymbol3, emptyComponentObject "Root0.b1.c" componentSymbolC)] |> Map.ofList
                    })
                    (subcomponentSymbol2, {
                        emptyComponentObject "Root0.b2" componentSymbolB with
                            Subcomponents = [(subcomponentSymbol3, emptyComponentObject "Root0.b2.c" componentSymbolC)] |> Map.ofList
                    }) 
                ] |> Map.ofList
        }

        let partition1 = {
            emptyComponentObject "Root1" componentSymbolB with
                Subcomponents = [(subcomponentSymbol3, emptyComponentObject "Root1.c" componentSymbolC)] |> Map.ofList
        }

        let partition2 = emptyComponentObject "Root2" componentSymbolC
        let partitions = [partition0; partition1; partition2] |> List.map createPartition

        modelObject.Partitions =? partitions

[<TestFixture>]
module ``ResolveSymbol Method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        compile "class A : Component {}" ["A"]
        raisesArgumentNullException "componentObject" <@ objectResolver.ResolveSymbol null @>

    [<Test>]
    let ``throws when component of unknown type is passed`` () =
        compile "class A : Component {}" ["A"]
        raisesArgumentException "componentObject" <@ objectResolver.ResolveSymbol (EmptyComponent ()) @>

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
        test <@ obj.ReferenceEquals (objectResolver.ResolveSymbol components.[0], objectResolver.ResolveSymbol components.[1]) @>

[<TestFixture>]
module ``ResolveObject Method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        compile "class A : Component {}" ["A"]
        raisesArgumentNullException "componentObject" <@ objectResolver.ResolveObject null @>

    [<Test>]
    let ``throws when component of unknown type is passed`` () =
        compile "class A : Component {}" ["A"]
        raisesArgumentException "componentObject" <@ objectResolver.ResolveObject (EmptyComponent ()) @>

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