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

namespace SafetySharp.Tests.CSharp.IFieldSymbolTests

open System.Linq
open NUnit.Framework
open FsUnit
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp
open SafetySharp.Tests.CSharp

[<TestFixture>]
module IsSubcomponentFieldMethod =
    let isComponentField csharpCode =
        let compilation = TestCompilation csharpCode

        let classSymbol = compilation.SemanticModel.GetTypeSymbol "X"
        let fieldSymbol = classSymbol.GetMembers().OfType<IFieldSymbol>().Single()
            
        fieldSymbol.IsSubcomponentField compilation.SemanticModel

    [<Test>]
    let ``returns false for non-component fields`` () =
        isComponentField "class X : Component { int x; }" |> should be False
        isComponentField "class X : Component { bool x; }" |> should be False
        isComponentField "class X : Component { decimal x; }" |> should be False

    [<Test>]
    let ``returns true for component fields`` () =
        isComponentField "class X : Component { Component x; }" |> should be True
        isComponentField "class X : Component { IComponent x; }" |> should be True
        isComponentField "class Y : Component {} class X : Component { Y x; }" |> should be True
        isComponentField "interface Y : IComponent {} class X : Component { Y x; }" |> should be True