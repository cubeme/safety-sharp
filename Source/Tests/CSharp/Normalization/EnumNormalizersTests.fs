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

namespace SafetySharp.Tests.CSharp.Normalization.EnumNormalizersTests

open System
open System.Linq
open System.Threading
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Diagnostics
open SafetySharp.Internal.CSharp
open SafetySharp.Tests
open SafetySharp.Internal.CSharp.Normalization
open SafetySharp.Internal.CSharp.Roslyn

[<TestFixture>]
module EnumTypeNormalizerTests =

    let normalize csharpCode =
        let compilation = TestCompilation ("enum E { A } " + csharpCode)
        let syntaxTree = EnumTypeNormalizer().Normalize(compilation.CSharpCompilation).SyntaxTrees.Single ()
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single().ToFullString ()

    [<Test>]
    let ``does not change references to non-enum types`` () =
        normalize "class X : Component { int i; bool b; decimal d; extern bool M(int i, decimal d); }" =?
            "class X : Component { int i; bool b; decimal d; extern bool M(int i, decimal d); }"

    [<Test>]
    let ``does not change references to enum literals`` () =
        normalize "class X : Component { int i = (int)E.A; }" =? "class X : Component { int i = (int)E.A; }"

    [<Test>]
    let ``does not change references to enum types outside of components`` () =
        normalize "class X { E a; int i; bool b; decimal d; extern bool M(int i, decimal d, E a); }" =?
            "class X { E a; int i; bool b; decimal d; extern bool M(int i, decimal d, E a); }"

    [<Test>]
    let ``replaces enum field declarations`` () =
        normalize "class C : Component { E a; E a1, a2; }" =? "class C : Component { int a; int a1, a2; }"

    [<Test>]
    let ``replaces enum return types`` () =
        normalize "class C : Component { extern E M(); E N() { return E.A; }}" =? 
            "class C : Component { extern int M(); int N() { return E.A; }}"

    [<Test>]
    let ``replaces enum parameters`` () =
        normalize "class C : Component { extern void M(E e1, E e2); void N(E e) {}}" =? 
            "class C : Component { extern void M(int e1, int e2); void N(int e) {}}"

    [<Test>]
    let ``replaces enum used as generic argument`` () =
        normalize "struct X<T> {} class C : Component { void M(X<E> x) {} }" =? "class C : Component { void M(X<int> x) {} }"

    [<Test>]
    let ``replaces enum casts`` () =
        normalize "class C : Component { E e = (E)0; }" =? "class C : Component { int e = (int)0; }"

    [<Test>]
    let ``replaces use of enum type in 'default' expression`` () =
        normalize "class C : Component { E M() { return default(E); }}" =? "class C : Component { int M() { return default(int); }}"

    [<Test>]
    let ``replaces enum local variable declarations`` () =
        normalize "class C : Component { void M() { E e; }}" =? "class C : Component { void M() { int e; }}"
        normalize "class C : Component { void M() { E e1, e2; }}" =? "class C : Component { void M() { int e1, e2; }}"
        normalize "class C : Component { void M() { E e = E.A; }}" =? "class C : Component { void M() { int e = E.A; }}"

[<TestFixture>]
module EnumLiteralNormalizerTests =

    let normalize csharpCode =
        let compilation = TestCompilation ("enum E { A, B, C } " + csharpCode)
        let syntaxTree = EnumLiteralNormalizer().Normalize(compilation.CSharpCompilation).SyntaxTrees.Single ()
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single().ToFullString ()

    [<Test>]
    let ``does not change non-enum member accesses`` () =
        normalize "class X : Component { int i = X.s; static int s; int M() { return X.s; }}" =?
            "class X : Component { int i = X.s; static int s; int M() { return X.s; }}"

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