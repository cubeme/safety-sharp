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
open SafetySharp.Modeling
open SafetySharp.CSharpCompiler.Normalization
open SafetySharp.CSharpCompiler.Roslyn.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols

[<TestFixture>]
module LocalDeclarationNormalizer =
    let normalize = TestCompilation.GetNormalizedClass (LocalDeclarationNormalizer ())

    [<Test>]
    let ``does not normalize variable declarations of method not declared within a component class`` () =
        normalize "class X { void M() { int x, y; }}" =? "class X { void M() { int x, y; }}"

    [<Test>]
    let ``does not change single variable declaration of component method`` () =
        normalize "class X : Component { void M() { int x; }}" =? "class X : Component { void M() { int x; }}"

    [<Test>]
    let ``normalizes variable declarations without initializers within a component`` () =
        normalize "class X : Component { void M() { int x, y; }}" =? "class X : Component { void M() { int x; int y; }}"
        normalize "class X : Component { void M() { int x, y, z, w; }}" =? "class X : Component { void M() { int x; int y; int z; int w; }}"

    [<Test>]
    let ``normalizes variable declarations with initializers within a component`` () =
        normalize "class X : Component { void M() { int x, y = 1; }}" =? "class X : Component { void M() { int x; int y = 1; }}"
        normalize "class X : Component { void M() { int x, y = 17, z, w = 44; }}" =? 
            "class X : Component { void M() { int x; int y = 17; int z; int w = 44; }}"

    [<Test>]
    let ``normalizes variable declarations within nested blocks`` () =
        normalize "class X : Component { void M() { int x, y; { int a, b; }}}" =?
            "class X : Component { void M() { int x; int y; { int a; int b; }}}"

    [<Test>]
    let ``normalizes multiple variable declarations nested within other statements`` () =
        normalize "class X : Component { void M() { int a = 0; a++; bool x, y; a--; int z, w; }}" =?
            "class X : Component { void M() { int a = 0; a++; bool x; bool y; a--; int z; int w; }}"

    [<Test>]
    let ``normalizes multiple variable declarations in nested blocks within a component`` () =
        normalize "class X : Component { void M() { int x, y = 1; x = y; bool z, w = x != y; { int a = 0, b = 0; z = a == b; }}}" =?
            "class X : Component { void M() { int x; int y = 1; x = y; bool z; bool w = x != y; { int a = 0; int b = 0; z = a == b; }}}"
