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
module EnumLiteralNormalizer =
    let normalize csharpCode =
        let compilation = TestCompilation ("enum E { A, B, C } " + csharpCode)
        let syntaxTree = EnumLiteralNormalizer().Normalize(compilation.CSharpCompilation).SyntaxTrees.Single ()
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single().ToFullString ()

    [<Test>]
    let ``does not change non-enum member accesses`` () =
        normalize "class X : Component { int i = X.s; static int s; int M() { return X.s; }}" =?
            "class X : Component { int i = X.s; static int s; int M() { return X.s; }}"

        normalize "class X : Component { int Y { get; set; } int M() { return this.Y; }}" =?
            "class X : Component { int Y { get; set; } int M() { return this.Y; }}"

    [<Test>]
    let ``does not change references to enum literals outside of components`` () =
     normalize "class X { E e = E.A; }" =? "class X { E e = E.A; }"

    [<Test>]
    let ``replaces enum literal in field declaration`` () =
     normalize "class C : Component { E e = E.A; E e1 = E.B, e2 = E.C; }" =? "class C : Component { E e = 0; E e1 = 1, e2 = 2; }"

    [<Test>]
    let ``replaces enum literal default method parameter`` () =
     normalize "class C : Component { void M(E e = E.C) {} }" =? "class C : Component { void M(E e = 2) {} }"

    [<Test>]
    let ``replaces enum literal in local variable initializer`` () =
        normalize "class C : Component { void M() { E e = E.B; }}" =? "class C : Component { void M() { E e = 1; }}"
        normalize "class C : Component { void M() { E e1 = E.B, e2 = E.C; }}" =? "class C : Component { void M() { E e1 = 1, e2 = 2; }}"

    [<Test>]
    let ``replaces enum literal method parameter`` () =
        normalize "class C : Component { void M(E e) { M(E.B); }}" =? "class C : Component { void M(E e) { M(1); }}"

    [<Test>]
    let ``replaces enum literal in equality comparison`` () =
        normalize "class C : Component { bool M() { return E.A == E.C; }}" =? "class C : Component { bool M() { return 0 == 2; }}"

    [<Test>]
    let ``replaces enum in switch case labels`` () =
        normalize "class C : Component { void M(E e) { switch (e) { case E.A: return; case E.B: return; case E.C: return; } }}" =?
            "class C : Component { void M(E e) { switch (e) { case 0: return; case 1: return; case 2: return; } }}"