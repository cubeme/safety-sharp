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
open SafetySharp.CSharpCompiler.Roslyn
open SafetySharp.CSharpCompiler.Roslyn.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols

[<TestFixture>]
module ExpressionPropertyNormalizer =
    let normalize csharpCode = 
        TestCompilation.GetNormalizedClass (ExpressionPropertyNormalizer()) 
            (csharpCode + "interface I { int B { get; } } namespace N { interface I { int B { get; } } }")

    [<Test>]
    let ``does not normalize properties of non-component classes`` () =
        normalize "class X { bool B => false; }" =? "class X { bool B => false; }"

    [<Test>]
    let ``does not normalize properties with accessors`` () =
        normalize "class X : Component { bool B { get { return false; } } }" =? "class X : Component { bool B { get { return false; } } }"
        normalize "class X : Component { bool B { set { } } }" =? "class X : Component { bool B { set { } } }"
        normalize "class X : Component { bool B { get { return false; } set { } } }" 
            =? "class X : Component { bool B { get { return false; } set { } } }"

    [<Test>]
    let ``normalize properties with expression bodies`` () =
        normalize "class X : Component { bool B => true; }" =? "class X : Component { bool B { get { return true; } } }"
        normalize "class X : Component { public int B => 1; }" =? "class X : Component { public int B { get { return 1; } } }"
        normalize "class X : Component { [Required] public int B => 1; }" =? 
            "class X : Component { [Required] public int B { get { return 1; } } }"
        normalize "class X : Component { [Required, Provided] public int B => 1; }" =? 
            "class X : Component { [Required, Provided] public int B { get { return 1; } } }"
        normalize "class X : Component { [Required] [Provided] public int B => 1; }" =? 
            "class X : Component { [Required] [Provided] public int B { get { return 1; } } }"

    [<Test>]
    let ``normalize explicitly implemented properties with expression bodies`` () =
        normalize "class X : Component, I { int I.B => 13; }" =? "class X : Component, I { int I.B { get { return 13; } } }"
        normalize "class X : Component, N.I { int N.I.B => 1; }" =? "class X : Component, N.I { int N.I.B { get { return 1; } } }"
        normalize "class X : Component, N.I { [Required] int N.I.B => 1; }" =? 
            "class X : Component, N.I { [Required] int N.I.B { get { return 1; } } }"
        normalize "class X : Component, I { [Required, Provided] int I.B => 1; }" =? 
            "class X : Component, I { [Required, Provided] int I.B { get { return 1; } } }"
        normalize "class X : Component, I { [Required] [Provided] int I.B => 1; }" =? 
            "class X : Component, I { [Required] [Provided] int I.B { get { return 1; } } }"
