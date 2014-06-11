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

namespace SafetySharp.Tests.CSharp.SymbolMapTests

open System
open System.Linq
open NUnit.Framework
open FsUnit
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp
open SafetySharp.Metamodel
open SafetySharp.Tests.CSharp

[<AutoOpen>]
module private SymbolMapTestsHelper =
    let compile csharpCode components =
        let compilation = TestCompilation csharpCode
        SymbolMap (compilation.CSharpCompilation, components)

    let components csharpCode components =
        let symbolMap = compile csharpCode components
        symbolMap.Components

    let emptyUpdate = { Name = "Update"; ReturnType = None; Parameters = [] }
    let emptyComponent name = { Name = "TestCompilation::" + name; UpdateMethod = emptyUpdate; Fields = []; Methods = []; Subcomponents = [] } 

[<TestFixture>]
module Constructor =
    [<Test>]
    let ``throws when no components are provided`` () =
        (fun () -> compile "class C : Component {}" [] |> ignore) |> should throw typeof<ArgumentException>

    [<Test>]
    let ``throws when non-component is provided`` () =
        (fun () -> compile "class C {}" [ "C" ] |> ignore) |> should throw typeof<InvalidOperationException>

[<TestFixture>]
module ComponentsProperty =
    [<Test>]
    let ``contains all components`` () =
        components "class A : Component {} class B : Component {} class C : Component {}" [ "A"; "B"; "C" ]
        |> should equal [ emptyComponent "A"; emptyComponent "B"; emptyComponent "C" ]

    [<Test>]
    let ``does not contain ignored components`` () =
        components "class A : Component {} class B : Component {} class C : Component {}" [ "A"; "C" ]
        |> should equal [ emptyComponent "A"; emptyComponent "C" ]

    [<Test>]
    let ``contains components that are provided multiple times only once`` () =
        components "class A : Component {} class B : Component {} class C : Component {}" [ "C"; "A"; "C" ]
        |> should equal [ emptyComponent "C"; emptyComponent "A" ]