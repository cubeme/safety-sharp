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
module InterfaceRequiredPortNormalizer =
    let normalize csharpCode = 
        TestCompilation.GetNormalizedInterface (InterfaceRequiredPortNormalizer ()) ("using System.Diagnostics;" + csharpCode)

    [<Test>]
    let ``does not normalize required port not declared within a component interface`` () =
        normalize "interface X { [Required] void M(); }" =? "interface X { [Required] void M(); }"

    [<Test>]
    let ``does not normalize non-required port component interface method`` () =
        normalize "interface X : IComponent { void M(); }" =? "interface X : IComponent { void M(); }"

    [<Test>]
    let ``normalizes required 'void -> void' port within a component interface`` () =
        normalize "interface X : IComponent { [Required] void M(); }" =? 
            "interface X : IComponent { [Required] System.Action M { set; } }"

    [<Test>]
    let ``normalizes required void returning port within a component interface`` () =
        normalize "interface X : IComponent { [Required] void M(int a); }" =? 
            "interface X : IComponent { [Required] System.Action<int> M { set; } }"
        normalize "interface X : IComponent { [Required] void M(int a, decimal b); }" =? 
            "interface X : IComponent { [Required] System.Action<int, decimal> M { set; } }"
        normalize "interface X : IComponent { [Required] void M(int a, decimal b, bool c); }" =? 
            "interface X : IComponent { [Required] System.Action<int, decimal, bool> M { set; } }"

    [<Test>]
    let ``normalizes required non-void returning port within a component interface`` () =
        normalize "interface X : IComponent { [Required] bool M(int a); }" =? 
            "interface X : IComponent { [Required] System.Func<int, bool> M { set; } }"
        normalize "interface X : IComponent { [Required] int M(int a, decimal b); }" =? 
            "interface X : IComponent { [Required] System.Func<int, decimal, int> M { set; } }"
        normalize "interface X : IComponent { [Required] bool M(int a, decimal b, bool c); }" =? 
            "interface X : IComponent { [Required] System.Func<int, decimal, bool, bool> M { set; } }"

    [<Test>]
    let ``preserves attributes applied to required port within a component interface`` () =
        normalize "interface X : IComponent { [DebuggerHidden, Required] void M(); }" =?
            "interface X : IComponent { [DebuggerHidden, Required] System.Action M { set; } }"

        normalize "interface X : IComponent { [DebuggerHidden, Required, DebuggerNonUserCode] void M(); }" =?
            "interface X : IComponent { [DebuggerHidden, Required, DebuggerNonUserCode] System.Action M { set; } }"

        normalize "interface X : IComponent { [DebuggerHidden] [Required] [DebuggerNonUserCode] void M(); }" =?
            "interface X : IComponent { [DebuggerHidden] [Required] [DebuggerNonUserCode] System.Action M { set; } }"

    [<Test>]
    let ``preserves line numbers of following lines`` () =
        let actual = normalize "interface X : IComponent { [Required] void M(int a,\nint b,\nint c); \n\nint N(); }" |> normalizeNewLines
        let expected = "interface X : IComponent { [Required] System.Action<int, int, int> M { set; } \n\n\n\nint N(); }"

        actual =? expected