// The MIT License (MIT)
// open SafetySharp.Modeling
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

namespace Roslyn.Syntax.SyntaxNodeExtensions

open System
open System.Linq
open System.Runtime.CompilerServices
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.CSharp
open SafetySharp.Modeling.CompilerServices
open SafetySharp.CSharpCompiler.Roslyn.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols

[<AutoOpen>]
module Helpers =
    let toString (node : SyntaxNode) =
        node.ToFullString().Replace ("\r", String.Empty)

[<TestFixture>]
module ``GetReferencedSymbol`` =
    let mutable compilation : TestCompilation = null

    let getReferencedSymbol<'T when 'T :> ISymbol and 'T : not struct> csharpCode =
        compilation <- TestCompilation (sprintf "class X { int f; int P { get; set; } int M() { return %s; }}" csharpCode)
        let expression = compilation.SyntaxRoot.Descendants<ReturnStatementSyntax>().Single().Expression

        expression.GetReferencedSymbol<'T> compilation.SemanticModel

    [<Test>]
    let ``throws when syntax node is null`` () =
        let compilation = TestCompilation ""
        raisesArgumentNullException "syntaxNode" (fun () -> (null : SyntaxNode).GetReferencedSymbol compilation.SemanticModel |> ignore)

    [<Test>]
    let ``throws when semantic model is null`` () =
        let node = SyntaxFactory.ParseExpression "1 + 1"
        raisesArgumentNullException "semanticModel" (fun () -> node.GetReferencedSymbol null |> ignore)

    [<Test>]
    let ``throws when syntax node does not reference any symbol`` () =
        raises<NullReferenceException> (fun () -> getReferencedSymbol<IMethodSymbol> "1" |> ignore)

    [<Test>]
    let ``throws when syntax node references symbol of different kind`` () =
        raises<InvalidCastException> (fun () -> getReferencedSymbol<IMethodSymbol> "f" |> ignore)

    [<Test>]
    let ``returns referenced field symbol`` () =
        getReferencedSymbol<IFieldSymbol> "f" =? compilation.FindFieldSymbol "X" "f"

    [<Test>]
    let ``returns referenced property symbol`` () =
        getReferencedSymbol<IPropertySymbol> "P" =? compilation.FindPropertySymbol "X" "P"

    [<Test>]
    let ``returns referenced method symbol`` () =
        getReferencedSymbol<IMethodSymbol> "M()" =? compilation.FindMethodSymbol "X" "M"

[<TestFixture>]
module ``AsSingleLine method`` =
    
    let asSingleLine csharpCode =
        SyntaxFactory.ParseStatement(csharpCode).AsSingleLine() |> toString

    [<Test>]
    let ``throws when null is passed`` () =
        raisesArgumentNullException "syntaxNode" (fun () -> (null : SyntaxNode).AsSingleLine () |> ignore)

    [<Test>]
    let ``does not modify single line statements`` () =
        asSingleLine "var x = 1;" =? "var x = 1;"
        asSingleLine "if (true) ; else return;" =? "if (true) ; else return;"

    [<Test>]
    let ``modifies multi-line statements`` () =
        asSingleLine "var\nx =\n1;" =? "var x = 1;"
        asSingleLine "if\n(true)\n; else\nreturn;" =? "if (true) ; else return;"

[<TestFixture>]
module ``EnsureSameLineCount method`` =

    let ensureSameLineCount csharpCode templateCSharpCode =
        let templateNode = SyntaxFactory.ParseStatement templateCSharpCode
        SyntaxFactory.ParseStatement(csharpCode).EnsureSameLineCount(templateNode) |> toString

    [<Test>]
    let ``throws when syntax node is null`` () =
        raisesArgumentNullException "syntaxNode" (fun () -> (null : SyntaxNode).EnsureSameLineCount (SyntaxFactory.ParseExpression "1") |> ignore)

    [<Test>]
    let ``throws when template node is null`` () =
        raisesArgumentNullException "templateNode" (fun () -> (SyntaxFactory.ParseExpression "1").EnsureSameLineCount null |> ignore)

    [<Test>]
    let ``throws when syntax node has more lines than template node`` () =
        let syntaxNode = SyntaxFactory.ParseExpression "1 +\n 1"
        let templateNode = SyntaxFactory.ParseExpression "1 + 1"
        raises<InvalidOperationException> (fun () -> syntaxNode.EnsureSameLineCount templateNode |> ignore)

    [<Test>]
    let ``does not modify syntax node when line counts match`` () =
        ensureSameLineCount "var x = 1;" "    var x =   1;" =? "var x = 1;"
        ensureSameLineCount "if (true) ; else return;" "var y = 1 + 1" =? "if (true) ; else return;"

    [<Test>]
    let ``adds trailing new lines when syntax node has less lines than template node`` () =
        ensureSameLineCount "var x = 1;" " var x \n=   1;" =? "var x = 1;\n"
        let actual = ensureSameLineCount "if (true) ; else return;" "if \n(true) \n;\n else\n return;\n"
        let expected = "if (true) ; else return;\n\n\n\n"

        actual =? expected
