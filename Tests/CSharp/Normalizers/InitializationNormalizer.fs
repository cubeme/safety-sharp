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
module InitializationNormalizer =
    let normalize = TestCompilation.GetNormalizedClass (InitializationNormalizer ())

    [<Test>]
    let ``does not normalize variable declaration of method not declared within a component class`` () =
        normalize "class X { void M() { int x; }}" =? "class X { void M() { int x; }}"

    [<Test>]
    let ``does not change initialized variable declaration with a component class`` () =
        normalize "class X : Component { void M() { int x = 0; }}" =? "class X : Component { void M() { int x = 0; }}"
        normalize "class X : Component { void M() { int x = 0, y = 1; }}" =? "class X : Component { void M() { int x = 0, y = 1; }}"

    [<Test>]
    let ``normalizes uninitialized variable declaration within a component`` () =
        normalize "class X : Component { void M() { int x; }}" =? "class X : Component { void M() { int x = default (int); }}"
        normalize "class X : Component { void M() { int x, y, z; }}" =? 
            "class X : Component { void M() { int x = default (int), y = default (int), z = default (int); }}"
        normalize "class X : Component { void M() { bool a = false, b, c, d = true; }}" =? 
            "class X : Component { void M() { bool a = false, b = default (bool), c = default (bool), d = true; }}"
