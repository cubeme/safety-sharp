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

namespace Roslyn.Symbols.FieldSymbolExtensions

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols

[<TestFixture>]
module ``IsSubcomponentField methods`` =
    let isComponentField csharpCode =
        let compilation = TestCompilation csharpCode

        let classSymbol = compilation.CSharpCompilation.GetTypeSymbol "X"
        let fieldSymbol = classSymbol.GetMembers().OfType<IFieldSymbol>().Single()
            
        fieldSymbol.IsSubcomponentField compilation.SemanticModel && fieldSymbol.IsSubcomponentField compilation.CSharpCompilation

    [<Test>]
    let ``throws if field symbol is null`` () =
        let compilation = TestCompilation ""
        raisesArgumentNullException "fieldSymbol" (fun () -> (null : IFieldSymbol).IsSubcomponentField compilation.CSharpCompilation |> ignore)
        raisesArgumentNullException "fieldSymbol" (fun () -> (null : IFieldSymbol).IsSubcomponentField compilation.SemanticModel |> ignore)

    [<Test>]
    let ``throws if semantic model is null`` () =
        let compilation = TestCompilation "class C { int x; }"
        let fieldSymbol = compilation.FindFieldSymbol "C" "x"
        raisesArgumentNullException "semanticModel" (fun () -> fieldSymbol.IsSubcomponentField (null : SemanticModel) |> ignore)

    [<Test>]
    let ``throws if compilation is null`` () =
        let compilation = TestCompilation "class C { int x; }"
        let fieldSymbol = compilation.FindFieldSymbol "C" "x"
        raisesArgumentNullException "compilation" (fun () -> fieldSymbol.IsSubcomponentField (null : Compilation) |> ignore)

    [<Test>]
    let ``returns false for non-component fields`` () =
        isComponentField "class X : Component { int x; }" =? false
        isComponentField "class X : Component { bool x; }" =? false
        isComponentField "class X : Component { decimal x; }" =? false

    [<Test>]
    let ``returns true for component fields`` () =
        isComponentField "class X : Component { Component x; }" =? true
        isComponentField "class X : Component { IComponent x; }" =? true
        isComponentField "class Y : Component {} class X : Component { Y x; }" =? true
        isComponentField "interface Y : IComponent {} class X : Component { Y x; }" =? true