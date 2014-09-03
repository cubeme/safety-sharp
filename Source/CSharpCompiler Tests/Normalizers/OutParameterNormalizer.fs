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

namespace Normalization

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Diagnostics
open SafetySharp.Tests
open SafetySharp.Modeling
open SafetySharp.CSharpCompiler.Normalization
open SafetySharp.CSharpCompiler.Roslyn.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols

[<TestFixture>]
module OutParameterNormalizer =
    let normalize csharpCode = 
        let compilation = TestCompilation csharpCode
        let syntaxTree = OutParameterNormalizer().Normalize(compilation.CSharpCompilation).SyntaxTrees.Single ()
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single().ToFullString ()

    [<Test>]
    let ``does not normalize out parameters of method not declared within a component class`` () =
        normalize "class X { void M(out int x) { x = 1; }}" =? "class X { void M(out int x) { x = 1; }}"

    [<Test>]
    let ``does not normalize out arguments of method invocation outisde a component class`` () =
        normalize "class X { void M(out int x) { x = 1; M(out x); }}" =? "class X { void M(out int x) { x = 1; M(out x); }}"

    [<Test>]
    let ``does not change component method without out parameters`` () =
        normalize "class X : Component { void M(int x, ref int y) {}}" =? "class X : Component { void M(int x, ref int y) {}}"

    [<Test>]
    let ``does not change method invocation without out parameters within a component`` () =
        normalize "class X : Component { void M(int x, ref int y) { M(0, ref x); }}" =? 
            "class X : Component { void M(int x, ref int y) { M(0, ref x); }}"

    [<Test>]
    let ``normalizes component methods with out parameters within a component`` () =
        normalize "class X : Component { void M(out int x) { x = 0; }}" =? "class X : Component { void M(ref int x) { x = 0; }}"
        normalize "class X : Component { void M(int a, out int x, int b) { x = 0; }}" =? 
            "class X : Component { void M(int a, ref int x, int b) { x = 0; }}"
        normalize "class X : Component { void M(ref int a, out int x, out int y) { x = 0; y = 0; }}" =? 
            "class X : Component { void M(ref int a, ref int x, ref int y) { x = 0; y = 0; }}"

    [<Test>]
    let ``normalizes method invocations with out parameters within a component`` () =
        normalize "class X : Component { void M(out int x) { M(out x); }}" =? "class X : Component { void M(ref int x) { M(ref x); }}"
        normalize "class X : Component { void M(int a, out int x, int b) { M(a, out x, b); }}" =? 
            "class X : Component { void M(int a, ref int x, int b) { M(a, ref x, b); }}"
        normalize "class X : Component { void M(ref int a, out int x, out int y) { M(ref a, out x, out y); }}" =? 
            "class X : Component { void M(ref int a, ref int x, ref int y) { M(ref a, ref x, ref y); }}"
