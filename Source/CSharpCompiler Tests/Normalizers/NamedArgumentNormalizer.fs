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
module NamedArgumentNormalizer =
    let normalize csharpCode = 
        let compilation = TestCompilation csharpCode
        let syntaxTree = NamedArgumentNormalizer().Normalize(compilation.CSharpCompilation).SyntaxTrees.Single ()
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single().ToFullString ()

    [<Test>]
    let ``does not normalize named arguments of method invocation outside a component class`` () =
        normalize "class X { void M(int a, int b) { M(b: 1, a: 2); }}" =? "class X { void M(int a, int b) { M(b: 1, a: 2); }}"

    [<Test>]
    let ``does not reorder arguments of invocations within a component when order is correct`` () =
        normalize "class X : Component { void M(int x, int y) { M(x: 2, y: 3); } void N() { N(); }}" =? 
            "class X : Component { void M(int x, int y) { M(2, 3); } void N() { N(); }}"
        normalize "class X : Component { void M(int x, int y) { M(2, y: 3); }}" =? 
            "class X : Component { void M(int x, int y) { M(2, 3); }}"

    [<Test>]
    let ``reorders named arguments of invocations within a component`` () =
        normalize "class X : Component { void M(int x, int y, int z) { M(y: 2, x: 1, z: 3); }}" =? 
            "class X : Component { void M(int x, int y, int z) { M(1, 2, 3); }}"
        normalize "class X : Component { void M(int x, int y, int z) { M(2, z: 1, y: 3); }}" =? 
            "class X : Component { void M(int x, int y, int z) { M(2, 3, 1); }}"
        normalize "class X : Component { void M(int x, int y, int z) { M(z: 2, x: 1, y: 3); }}" =? 
            "class X : Component { void M(int x, int y, int z) { M(1, 3, 2); }}"
        normalize "class X : Component { void M(int x, int y, int z) { M(z: 2, y: 1, x: 3); }}" =? 
            "class X : Component { void M(int x, int y, int z) { M(3, 1, 2); }}"

    [<Test>]
    let ``reorders named arguments of nested invocations within a component`` () =
        normalize "class X : Component { int M(int a, int b) { return M(b: M(b: 17, a: 1), a: 2); }}" =?
            "class X : Component { int M(int a, int b) { return M(2, M(1, 17)); }}"
        normalize "class X : Component { int M(int a, int b) { return M(M(b: 17, a: 1), b: 2); }}" =?
            "class X : Component { int M(int a, int b) { return M(M(1, 17), 2); }}"
        normalize "class X : Component { int M(int a, int b) { return M(M(b: 17, a: 1), 2); }}" =?
            "class X : Component { int M(int a, int b) { return M(M(1, 17), 2); }}"
        normalize "class X : Component { int M(int a, int b) { return M(b: M(17, b: 1), a: 2); }}" =?
            "class X : Component { int M(int a, int b) { return M(2, M(17, 1)); }}"