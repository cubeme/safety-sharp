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

namespace Roslyn.Syntax.VariableDeclaratorExtensions

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Modeling.CompilerServices
open SafetySharp.CSharpCompiler.Roslyn.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols

[<TestFixture>]
module ``GetDeclaredSymbol method`` =
    [<Test>]
    let ``throws when variable declarator is null`` () =
        let compilation = TestCompilation ""
        raisesArgumentNullException "variableDeclarator" 
            (fun () -> (null : VariableDeclaratorSyntax).GetDeclaredSymbol compilation.SemanticModel |> ignore)

    [<Test>]
    let ``throws when semantic model is null`` () =
        let compilation = TestCompilation "class X { int f; }"
        let declaration = compilation.SyntaxRoot.Descendants<VariableDeclaratorSyntax>().Single ()
        raisesArgumentNullException "semanticModel" (fun () -> declaration.GetDeclaredSymbol null |> ignore)

    [<Test>]
    let ``throws when declared symbol is of different type`` () =
        let compilation = TestCompilation "class X { int f; }"
        let field = compilation.SyntaxRoot.Descendants<VariableDeclaratorSyntax>().Single ()

        raises<InvalidOperationException> (fun () -> field.GetDeclaredSymbol<ILocalSymbol> compilation.SemanticModel |> ignore)

    [<Test>]
    let ``returns declared field symbols`` () =
        let compilation = TestCompilation "class X { int f1, f2; }"
        let declarations = compilation.SyntaxRoot.Descendants<VariableDeclaratorSyntax>()
        let field1 = declarations.First ()
        let field2 = declarations.Skip(1).Single ()

        field1.GetDeclaredSymbol<IFieldSymbol> compilation.SemanticModel =? compilation.FindFieldSymbol "X" "f1"
        field2.GetDeclaredSymbol<IFieldSymbol> compilation.SemanticModel =? compilation.FindFieldSymbol "X" "f2"

    [<Test>]
    let ``returns declared local symbols`` () =
        let compilation = TestCompilation "class X { void M() { int f1, f2; }}"
        let declarations = compilation.SyntaxRoot.Descendants<VariableDeclaratorSyntax>()
        let local1 = declarations.First ()
        let local2 = declarations.Skip(1).Single ()

        local1.GetDeclaredSymbol<ILocalSymbol> compilation.SemanticModel =? compilation.FindLocalSymbol "X" "M" "f1"
        local2.GetDeclaredSymbol<ILocalSymbol> compilation.SemanticModel =? compilation.FindLocalSymbol "X" "M" "f2"