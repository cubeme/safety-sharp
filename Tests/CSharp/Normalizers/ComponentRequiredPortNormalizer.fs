// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
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
module ComponentRequiredPortNormalizer =
    let normalize csharpCode = 
        TestCompilation.GetNormalizedClass (ComponentRequiredPortNormalizer()) (sprintf "using System.Diagnostics; %s" csharpCode)

    [<Test>]
    let ``does not normalize extern method not declared within a component class`` () =
        normalize "class X { extern void M(); }" =? "class X { extern void M(); }"

    [<Test>]
    let ``does not normalize non-extern component method`` () =
        normalize "class X : Component { public void M() {}}" =? "class X : Component { public void M() {}}"

    [<Test>]
    let ``normalizes extern 'void -> void' method within a component`` () =
        normalize "class X : Component { public extern void M(); }" =? 
            "class X : Component { public System.Action M { private get; set; } }"
        normalize "class X : Component { internal extern void M(); }" =? 
            "class X : Component { internal System.Action M { private get; set; } }"
        normalize "class X : Component { protected internal extern void M(); }" =? 
            "class X : Component { protected internal System.Action M { private get; set; } }"
        normalize "class X : Component { protected extern void M(); }" =? 
            "class X : Component { protected System.Action M { private get; set; } }"
        normalize "class X : Component { private extern void M(); }" =? 
            "class X : Component { private System.Action M { get; set; } }"

    [<Test>]
    let ``normalizes extern void returning method within a component`` () =
        normalize "class X : Component { public extern void M(int a); }" =? 
            "class X : Component { public System.Action<int> M { private get; set; } }"
        normalize "class X : Component { internal extern void M(int a, decimal b); }" =? 
            "class X : Component { internal System.Action<int, decimal> M { private get; set; } }"
        normalize "class X : Component { internal extern void M(int a, decimal b, bool c); }" =? 
            "class X : Component { internal System.Action<int, decimal, bool> M { private get; set; } }"

    [<Test>]
    let ``normalizes extern non-void returning method within a component`` () =
        normalize "class X : Component { public extern bool M(int a); }" =? 
            "class X : Component { public System.Func<int, bool> M { private get; set; } }"
        normalize "class X : Component { internal extern int M(int a, decimal b); }" =? 
            "class X : Component { internal System.Func<int, decimal, int> M { private get; set; } }"
        normalize "class X : Component { internal extern bool M(int a, decimal b, bool c); }" =? 
            "class X : Component { internal System.Func<int, decimal, bool, bool> M { private get; set; } }"

    [<Test>]
    let ``normalizes explictly implemented extern method within a component`` () =
        normalize "interface I { void M(); } class X : Component, I { extern void I.M(); }" =?
            "class X : Component, I { System.Action I.M { private get; set; } }"

    [<Test>]
    let ``preserves attributes applied to extern method within a component`` () =
        normalize "class X : Component { [DebuggerHidden] extern void M(); }" =?
            "class X : Component { [DebuggerHidden] private System.Action M { get; set; } }"

        normalize "class X : Component { [DebuggerHidden, DebuggerNonUserCode] extern void M(); }" =?
            "class X : Component { [DebuggerHidden, DebuggerNonUserCode] private System.Action M { get; set; } }"

        normalize "class X : Component { [DebuggerHidden] [DebuggerNonUserCode] extern void M(); }" =?
            "class X : Component { [DebuggerHidden] [DebuggerNonUserCode] private System.Action M { get; set; } }"

    [<Test>]
    let ``preserves line numbers of following lines`` () =
        let actual = normalize "class X : Component { public extern void M(int a,\nint b,\nint c); \n\nint f; }" |> normalizeNewLines
        let expected = "class X : Component { public System.Action<int, int, int> M { private get; set; } \n\n\n\nint f; }"

        actual =? expected