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

namespace SafetySharp.Tests.CSharp.Diagnostics

open System.Linq
open System.Threading
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Diagnostics
open SafetySharp.Internal.CSharp
open SafetySharp.Tests
open SafetySharp.Internal.CSharp.Diagnostics
open SafetySharp.Internal.CSharp.Roslyn

[<TestFixture>]
module EnumUnderlyingTypeAnalyzerTests =
    let hasDiagnostics = TestCompilation.HasDiagnostics (EnumUnderlyingTypeAnalyzer ())

    [<Test>]
    let ``implicit underlying type is valid`` () =
        hasDiagnostics "enum E { A }" =? false

    [<Test>]
    let ``byte as underlying type is invalid`` () =
        hasDiagnostics "enum E : byte { A }" =? true

    [<Test>]
    let ``int as underlying type is invalid`` () =
        hasDiagnostics "enum E : int { A }" =? true

    [<Test>]
    let ``long as underlying type is invalid`` () =
        hasDiagnostics "enum E : long { A }" =? true

    [<Test>]
    let ``sbyte as underlying type is invalid`` () =
        hasDiagnostics "enum E : sbyte { A }" =? true

    [<Test>]
    let ``short as underlying type is invalid`` () =
        hasDiagnostics "enum E : short { A }" =? true

    [<Test>]
    let ``uint as underlying type is invalid`` () =
        hasDiagnostics "enum E : uint { A }" =? true

    [<Test>]
    let ``ulong as underlying type is invalid`` () =
        hasDiagnostics "enum E : ulong { A }" =? true

    [<Test>]
    let ``ushort as underlying type is invalid`` () =
        hasDiagnostics "enum E : ushort { A }" =? true