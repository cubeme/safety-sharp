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
open SafetySharp.CSharpCompiler.Roslyn
open SafetySharp.CSharpCompiler.Roslyn.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols

[<TestFixture>]
module ExpressionMethodNormalizer =
    let normalize csharpCode = 
        TestCompilation.GetNormalizedClass (ExpressionMethodNormalizer()) 
            (csharpCode + "interface I { int B(int i); } namespace N { interface I { int B(int i); } interface J { int B<T>(int i) where T : struct; } }")

    [<Test>]
    let ``does not normalize methods of non-component classes`` () =
        normalize "class X { bool B() => false; }" =? "class X { bool B() => false; }"

    [<Test>]
    let ``does not normalize regular methods`` () =
        normalize "class X : Component { bool B() { return false; } }" =? "class X : Component { bool B() { return false; } }"
        normalize "class X : Component { int B(int i) { return i; } }" =? "class X : Component { int B(int i) { return i; } }"

    [<Test>]
    let ``normalizes methods with expression bodies`` () =
        normalize "class X : Component { bool B() => true; }" =? "class X : Component { bool B() { return true; } }"
        normalize "class X : Component { public int B(int i) => i; }" =? "class X : Component { public int B(int i) { return i; } }"
        normalize "class X : Component { public int B(int i) => i; }" =? "class X : Component { public int B(int i) { return i; } }"
        normalize "class X : Component { [Required] public int B(int i) => i; }" =? 
            "class X : Component { [Required] public int B(int i) { return i; } }"
        normalize "class X : Component { [Required, Provided] public int B(int i) => i; }" =? 
            "class X : Component { [Required, Provided] public int B(int i) { return i; } }"
        normalize "class X : Component { [Required] [Provided] public int B(int i) => i; }" =? 
            "class X : Component { [Required] [Provided] public int B(int i) { return i; } }"

    [<Test>]
    let ``normalizes explicitly implemented methods with expression bodies`` () =
        normalize "class X : Component, I { int I.B(int i) => 1; }" =? "class X : Component, I { int I.B(int i) { return 1; } }"
        normalize "class X : Component, I { int I.B(int i) => i; }" =? "class X : Component, I { int I.B(int i) { return i; } }"
        normalize "class X : Component, N.I { int N.I.B(int i) => i; }" =? "class X : Component, N.I { int N.I.B(int i) { return i; } }"
        normalize "class X : Component, N.I { [Required] int N.I.B(int i) => i; }" =? 
            "class X : Component, N.I { [Required] int N.I.B(int i) { return i; } }"
        normalize "class X : Component, N.I { [Required, Provided] int N.I.B(int i) => i; }" =? 
            "class X : Component, N.I { [Required, Provided] int N.I.B(int i) { return i; } }"
        normalize "class X : Component, N.I { [Required] [Provided] int N.I.B(int i) => i; }" =? 
            "class X : Component, N.I { [Required] [Provided] int N.I.B(int i) { return i; } }"

    [<Test>]
    let ``normalizes generic methods with expression bodies`` () =
        normalize "class X : Component { T B<T>(T t) => t; }" =? "class X : Component { T B<T>(T t) { return t; } }"
        normalize "class X : Component { [Provided] T B<T>(T t) => t; }" =? 
            "class X : Component { [Provided] T B<T>(T t) { return t; } }"

    [<Test>]
    let ``normalizes generic methods with expression bodies and type constraints`` () =
        normalize "class X : Component { public bool B<T>() where T : class => false; }" =? 
            "class X : Component { public bool B<T>() where T : class { return false; } }"

    [<Test>]
    let ``normalizes explicitly implemented generic methods with expression bodies`` () =
        normalize "class X : Component, N.J { int N.J.B<T>(int i) => i; }" =? 
            "class X : Component, N.J { int N.J.B<T>(int i) { return i; } }"
        normalize "class X : Component, N.J { [Required] int N.J.B<T>(int i) => i; }" =? 
            "class X : Component, N.J { [Required] int N.J.B<T>(int i) { return i; } }"
