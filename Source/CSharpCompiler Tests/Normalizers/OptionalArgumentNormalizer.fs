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
module OptionalArgumentNormalizer =
    let normalize = TestCompilation.GetNormalizedClass (OptionalArgumentNormalizer ())

    [<Test>]
    let ``does not normalize optional arguments of method invocation outside a component class`` () =
        normalize "class X { void M(int a = 0) { M(); }}" =? "class X { void M(int a = 0) { M(); }}"

    [<Test>]
    let ``does not change invocation of method without optional parameters within a component class`` () =
        normalize "class X : Component { void M(int x) { M(2); } void N() { N(); }}" =? 
            "class X : Component { void M(int x) { M(2); } void N() { N(); }}"

    [<Test>]
    let ``does not change invocation of method with optional parameters within a component class when all arguments are provided`` () =
        normalize "class X : Component { void M(int x = 0) { M(2); } void N(bool b = false, bool c = true) { N(true, false); }}" =? 
            "class X : Component { void M(int x = 0) { M(2); } void N(bool b = false, bool c = true) { N(true, false); }}"

    [<Test>]
    let ``adds omitted arguments to invocation without named arguments within a component`` () =
        normalize "class X : Component { void M(int a = 17) { M(); }}" =? "class X : Component { void M(int a = 17) { M(a: 17); }}"
        normalize "class X : Component { void M(bool a = true) { M(); }}" =? "class X : Component { void M(bool a = true) { M(a: true); }}"
        normalize "class X : Component { void M(decimal a = 3.14m) { M(); }}" =? "class X : Component { void M(decimal a = 3.14m) { M(a: 3.14m); }}"

    [<Test>]
    let ``adds omitted arguments to invocation with multiple arguments within a component`` () =
        normalize "class X : Component { void M(int a, int b = 17) { M(3); }}" =? 
            "class X : Component { void M(int a, int b = 17) { M(3, b: 17); }}"
        normalize "class X : Component { void M(int a, int b = 17, int c = 2) { M(3); }}" =? 
            "class X : Component { void M(int a, int b = 17, int c = 2) { M(3, b: 17, c: 2); }}"
        normalize "class X : Component { void M(int a = 0, int b = 17, int c = 2) { M(3); }}" =? 
            "class X : Component { void M(int a = 0, int b = 17, int c = 2) { M(3, b: 17, c: 2); }}"
        normalize "class X : Component { void M(int a = 0, int b = 17, int c = 2) { M(3, 4); }}" =? 
            "class X : Component { void M(int a = 0, int b = 17, int c = 2) { M(3, 4, c: 2); }}"
        normalize "class X : Component { void M(int a = 0, int b = 17, int c = 2) { M(); }}" =? 
            "class X : Component { void M(int a = 0, int b = 17, int c = 2) { M(a: 0, b: 17, c: 2); }}"
        normalize "class X : Component { void M(int a = 0, int b = 17, int c = 2) { M(3, 2, 1); }}" =? 
            "class X : Component { void M(int a = 0, int b = 17, int c = 2) { M(3, 2, 1); }}"

    [<Test>]
    let ``adds omitted arguments with default values to invocation without named arguments within a component`` () =
        normalize "class X : Component { void M(int a = default(int)) { M(); }}" =? 
            "class X : Component { void M(int a = default(int)) { M(a: 0); }}"
        normalize "class X : Component { void M(bool a = default(bool)) { M(); }}" =? 
            "class X : Component { void M(bool a = default(bool)) { M(a: false); }}"
        normalize "class X : Component { void M(decimal a = default(decimal)) { M(); }}" =? 
            "class X : Component { void M(decimal a = default(decimal)) { M(a: 0m); }}"
        normalize "class X : Component { void M(System.DateTime a = default(System.DateTime)) { M(); }}" =? 
            "class X : Component { void M(System.DateTime a = default(System.DateTime)) { M(a: default (global::System.DateTime)); }}"

    [<Test>]
    let ``adds omitted arguments to invocation with named arguments within a component`` () =
        normalize "class X : Component { void M(int a = 0, int b = 17, int c = 2) { M(c: 3, a: 2); }}" =? 
            "class X : Component { void M(int a = 0, int b = 17, int c = 2) { M(c: 3, a: 2, b: 17); }}"
        normalize "class X : Component { void M(int a = 0, int b = 17, int c = 2) { M(3, b: 1); }}" =? 
            "class X : Component { void M(int a = 0, int b = 17, int c = 2) { M(3, b: 1, c: 2); }}"
        normalize "class X : Component { void M(int a = 0, int b = 17, int c = 2) { M(c: 3, a: 2, b: 1); }}" =? 
            "class X : Component { void M(int a = 0, int b = 17, int c = 2) { M(c: 3, a: 2, b: 1); }}"

    [<Test>]
    let ``adds omitted arguments to nested invocations within a component`` () =
        normalize "class X : Component { int M(int a = 1, int b = 2) { return M(b: M(b: 17)); }}" =?
            "class X : Component { int M(int a = 1, int b = 2) { return M(b: M(b: 17, a: 1), a: 1); }}"
        normalize "class X : Component { int M(int a = 1, int b = 2) { return M(M(17)); }}" =?
            "class X : Component { int M(int a = 1, int b = 2) { return M(M(17, b: 2), b: 2); }}"