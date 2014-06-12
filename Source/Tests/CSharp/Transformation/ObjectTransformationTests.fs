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

namespace SafetySharp.Tests.CSharp.ObjectTransformationTests

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

[<AutoOpen>]
module private ObjectTransformationTestsHelper =
    let mutable symbolResolver = Unchecked.defaultof<SymbolResolver>
    let mutable objectResolver = Unchecked.defaultof<ObjectResolver>
    let mutable components = Unchecked.defaultof<Component list>

    type TestModel (components) as this =
        inherit Model ()
        do this.SetPartitions (components |> Array.ofSeq)

    type EmptyComponent () =
        inherit Component ()

    let compile csharpCode componentTypes =
        let compilation = TestCompilation csharpCode
        symbolResolver <- SymbolTransformation.Transform compilation.CSharpCompilation
        components <- componentTypes |> List.map compilation.CreateObject

        let model = TestModel (components)
        model.FinalizeMetadata ()

        objectResolver <- ObjectTransformation.Transform model symbolResolver

    let createComponentObject name symbol = { Name = name; ComponentSymbol = symbol; Fields = Map.empty; Subcomponents = Map.empty }

[<TestFixture>]
module ``Transform method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        let compilation = TestCompilation "class A : Component {}"
        let symbolResolver = SymbolTransformation.Transform compilation.CSharpCompilation
        raisesWith<ArgumentNullException> <@ ObjectTransformation.Transform null symbolResolver @> (fun e -> <@ e.ParamName = "model" @>)

    [<Test>]
    let ``throws when model metadata has not yet been finalized`` () =
        let compilation = TestCompilation "class A : Component {}"
        symbolResolver <- SymbolTransformation.Transform compilation.CSharpCompilation
        let model = TestModel [EmptyComponent ()]

        raisesWith<ArgumentException> <@ ObjectTransformation.Transform model symbolResolver @> (fun e -> <@ e.ParamName = "model" @>)

[<TestFixture>]
module ``ModelObject property`` =
    [<Test>]
    let ``empty when compilation contains no components`` () =
        Assert.Fail "TODO"

[<TestFixture>]
module ``ResolveSymbol Method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        compile "class A : Component {}" ["A"]
        raisesWith<ArgumentNullException> <@ objectResolver.ResolveSymbol null @> (fun e -> <@ e.ParamName = "componentObject" @>)

    [<Test>]
    let ``throws when component of unknown type is passed`` () =
        compile "class A : Component {}" ["A"]
        raisesWith<ArgumentException> <@ objectResolver.ResolveSymbol (EmptyComponent ()) @> (fun e -> <@ e.ParamName = "componentObject" @>)

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
        raisesWith<ArgumentNullException> <@ objectResolver.ResolveObject null @> (fun e -> <@ e.ParamName = "componentObject" @>)

    [<Test>]
    let ``throws when component of unknown type is passed`` () =
        compile "class A : Component {}" ["A"]
        raisesWith<ArgumentException> <@ objectResolver.ResolveObject (EmptyComponent ()) @> (fun e -> <@ e.ParamName = "componentObject" @>)

    [<Test>]
    let ``returns component object for component object of known type`` () =
        compile "class A : Component {}" ["A"]
        objectResolver.ResolveObject components.[0] =? createComponentObject "Root0" symbolResolver.ComponentSymbols.[0]

    [<Test>]
    let ``returns different component symbols for different component objects of different known types`` () =
        compile "class A : Component {} class B : Component {}" ["A"; "B"]
        objectResolver.ResolveObject components.[0] =? createComponentObject "Root0" symbolResolver.ComponentSymbols.[0]
        objectResolver.ResolveObject components.[1] =? createComponentObject "Root1" symbolResolver.ComponentSymbols.[1]
        objectResolver.ResolveObject components.[0] <>? objectResolver.ResolveObject components.[1]

    [<Test>]
    let ``returns different component symbols for different component objects of same known type`` () =
        compile "class A : Component {}" ["A"; "A"]
        objectResolver.ResolveObject components.[0] =? createComponentObject "Root0" symbolResolver.ComponentSymbols.[0]
        objectResolver.ResolveObject components.[1] =? createComponentObject "Root1" symbolResolver.ComponentSymbols.[0]
        objectResolver.ResolveObject components.[0] <>? objectResolver.ResolveObject components.[1]