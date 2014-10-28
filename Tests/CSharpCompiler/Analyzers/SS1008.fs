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

namespace Analyzers

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Diagnostics
open SafetySharp.Tests
open SafetySharp.Modeling
open SafetySharp.CSharpCompiler.Analyzers
open SafetySharp.CSharpCompiler.Roslyn.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols

[<TestFixture>]
module SS1008 =
    let getDiagnostic = TestCompilation.GetDiagnostic (SS1008 ())

    let ss1008 location identifierName =
        Diagnostic ("SS1008", (1, location), (1, location + String.length identifierName), 
            sprintf "Identifier name '%s' is reserved for internal use." identifierName)
        |> Some

    [<Test>]
    let ``non-reserved names are valid`` () =
        getDiagnostic "enum E { A }" =? None
        getDiagnostic "interface I { void M(int a); int P { get; set; } }" =? None
        getDiagnostic "class C { void M(int a) { int b = a; } int P { get; set; } event System.EventHandler A; }" =? None
        getDiagnostic "struct C { void M(int a) { int b = a; } int P { get; set; } }" =? None
        getDiagnostic "namespace N {}" =? None
        getDiagnostic "namespace N.M {}" =? None

    [<Test>]
    let ``reserved names are invalid`` () =
        getDiagnostic "enum __E__ : byte { A }" =? ss1008 5 "__E__"
        getDiagnostic "enum E : byte { __A__ }" =? ss1008 16 "__A__"
        getDiagnostic "interface __I__ { void M(int a); int P { get; set; } }" =? ss1008 10 "__I__"
        getDiagnostic "interface I { void __M__(int a); int P { get; set; } }" =? ss1008 19 "__M__"
        getDiagnostic "interface I { void M(int __a__); int P { get; set; } }" =? ss1008 25 "__a__"
        getDiagnostic "interface I { void M(int a); int __P__ { get; set; } }" =? ss1008 33 "__P__"
        getDiagnostic "class __C__ { void M(int a) { int b = a; } int P { get; set; } }" =? ss1008 6 "__C__"
        getDiagnostic "class C { void __M__(int a) { int b = a; } int P { get; set; } }" =? ss1008 15 "__M__"
        getDiagnostic "class C { void M(int __a__) { int b = __a__; } int P { get; set; } }" =? ss1008 21 "__a__"
        getDiagnostic "class C { void M(int a) { int __b__ = a; } int P { get; set; } }" =? ss1008 30 "__b__"
        getDiagnostic "class C { void M(int a) { int b = a; } int __P__ { get; set; } }" =? ss1008 43 "__P__"
        getDiagnostic "class C { event System.EventHandler __E__; }" =? ss1008 36 "__E__"
        getDiagnostic "struct __S__ { void M(int a) { int b = a; } int P { get; set; } }" =? ss1008 7 "__S__"
        getDiagnostic "struct S { void __M__(int a) { int b = a; } int P { get; set; } }" =? ss1008 16 "__M__"
        getDiagnostic "struct S { void M(int __a__) { int b = __a__; } int P { get; set; } }" =? ss1008 22 "__a__"
        getDiagnostic "struct S { void M(int a) { int __b__ = a; } int P { get; set; } }" =? ss1008 31 "__b__"
        getDiagnostic "struct S { void M(int a) { int b = a; } int __P__ { get; set; } }" =? ss1008 44 "__P__"
        getDiagnostic "namespace __N__ {}" =? ss1008 10 "__N__"
        getDiagnostic "namespace __N__.M {}" =? ss1008 10 "__N__"
        getDiagnostic "namespace N.__M__ {}" =? ss1008 12 "__M__"
