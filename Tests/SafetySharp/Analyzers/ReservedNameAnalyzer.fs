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

namespace Analyzers

open System
open System.Linq
open NUnit.Framework
open SafetySharp.Modeling
open SafetySharp.Compiler.Analyzers
open SafetySharp.Compiler.Roslyn
open SafetySharp.Compiler.Roslyn.Syntax
open SafetySharp.Compiler.Roslyn.Symbols

[<TestFixture>]
module ``Rreserved names`` =
    let getDiagnostic = TestCompilation.GetDiagnostic (ReservedNameAnalyzer ())

    let diagnostic location identifierName =
        errorDiagnostic DiagnosticIdentifier.ReservedName (1, location) (1, location + String.length identifierName)
            "Identifier name '%s' is reserved for internal use." identifierName

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
        let invalidName = "Name".ToSynthesized ()
        getDiagnostic (sprintf "enum %s : byte { A }" invalidName) =? diagnostic 5 invalidName
        getDiagnostic (sprintf "enum E : byte { %s }"  invalidName)=? diagnostic 16 invalidName
        getDiagnostic (sprintf "interface %s { void M(int a); int P { get; set; } }"  invalidName)=? diagnostic 10 invalidName
        getDiagnostic (sprintf "interface I { void %s(int a); int P { get; set; } }"  invalidName)=? diagnostic 19 invalidName
        getDiagnostic (sprintf "interface I { void M(int %s); int P { get; set; } }"  invalidName)=? diagnostic 25 invalidName
        getDiagnostic (sprintf "interface I { void M(int a); int %s { get; set; } }"  invalidName)=? diagnostic 33 invalidName
        getDiagnostic (sprintf "class %s { void M(int a) { int b = a; } int P { get; set; } }" invalidName) =? diagnostic 6 invalidName
        getDiagnostic (sprintf "class C { void %s(int a) { int b = a; } int P { get; set; } }" invalidName) =? diagnostic 15 invalidName
        getDiagnostic (sprintf "class C { void M(int %s) { int b = 1; } int P { get; set; } }" invalidName) =? diagnostic 21 invalidName
        getDiagnostic (sprintf "class C { void M(int a) { int %s = a; } int P { get; set; } }" invalidName) =? diagnostic 30 invalidName
        getDiagnostic (sprintf "class C { void M(int a) { int %s = a, x; } int P { get; set; } }" invalidName) =? diagnostic 30 invalidName
        getDiagnostic (sprintf "class C { void M(int a) { int x, %s = a; } int P { get; set; } }" invalidName) =? diagnostic 33 invalidName
        getDiagnostic (sprintf "class C { void M(int a) { int b = a; } int %s { get; set; } }" invalidName) =? diagnostic 43 invalidName
        getDiagnostic (sprintf "class C { int %s; }" invalidName) =? diagnostic 14 invalidName
        getDiagnostic (sprintf "class C { int %s, a; }" invalidName) =? diagnostic 14 invalidName
        getDiagnostic (sprintf "class C { int a, %s; }" invalidName) =? diagnostic 17 invalidName
        getDiagnostic (sprintf "class C { event System.EventHandler %s; }" invalidName) =? diagnostic 36 invalidName
        getDiagnostic (sprintf "class C { event System.EventHandler %s, a; }" invalidName) =? diagnostic 36 invalidName
        getDiagnostic (sprintf "class C { event System.EventHandler a, %s; }" invalidName) =? diagnostic 39 invalidName
        getDiagnostic (sprintf "class C { event System.EventHandler %s { add {} remove {} } }" invalidName) =? diagnostic 36 invalidName
        getDiagnostic (sprintf "struct %s { void M(int a) { int b = a; } int P { get; set; } }" invalidName) =? diagnostic 7 invalidName
        getDiagnostic (sprintf "struct S { void %s(int a) { int b = a; } int P { get; set; } }" invalidName) =? diagnostic 16 invalidName
        getDiagnostic (sprintf "struct S { void M(int %s) { int b = 1; } int P { get; set; } }" invalidName) =? diagnostic 22 invalidName
        getDiagnostic (sprintf "struct S { void M(int a) { int %s = a; } int P { get; set; } }" invalidName) =? diagnostic 31 invalidName
        getDiagnostic (sprintf "struct S { void M(int a) { int %s = a, x; } int P { get; set; } }" invalidName) =? diagnostic 31 invalidName
        getDiagnostic (sprintf "struct S { void M(int a) { int x, %s = a; } int P { get; set; } }" invalidName) =? diagnostic 34 invalidName
        getDiagnostic (sprintf "struct S { void M(int a) { int b = a; } int %s { get; set; } }" invalidName) =? diagnostic 44 invalidName
        getDiagnostic (sprintf "struct S { int %s; }" invalidName) =? diagnostic 15 invalidName
        getDiagnostic (sprintf "struct S { int %s, a; }" invalidName) =? diagnostic 15 invalidName
        getDiagnostic (sprintf "struct S { int a, %s; }" invalidName) =? diagnostic 18 invalidName
        getDiagnostic (sprintf "struct S { event System.EventHandler %s; }" invalidName) =? diagnostic 37 invalidName
        getDiagnostic (sprintf "struct S { event System.EventHandler %s, a; }" invalidName) =? diagnostic 37 invalidName
        getDiagnostic (sprintf "struct S { event System.EventHandler a, %s; }" invalidName) =? diagnostic 40 invalidName
        getDiagnostic (sprintf "struct S { event System.EventHandler %s { add {} remove {} } }" invalidName) =? diagnostic 37 invalidName
        getDiagnostic (sprintf "namespace %s {}" invalidName) =? diagnostic 10 invalidName
        getDiagnostic (sprintf "namespace %s.M {}" invalidName) =? diagnostic 10 invalidName
        getDiagnostic (sprintf "namespace N.%s {}" invalidName) =? diagnostic 12 invalidName

    [<Test>]
    let ``reserved names within expressions are valid`` () =
        // Only emits a diagnostic for the declaration of the method parameter, but not for the usages of the parameter.
        let invalidName = "Name".ToSynthesized ()
        getDiagnostic (sprintf "class X { void M(int %s) { int b = %s + %s; } }" invalidName invalidName invalidName) =? diagnostic 21 invalidName
        getDiagnostic (sprintf "class %s { void M() { var t = typeof(%s); } }" invalidName invalidName) =? diagnostic 6 invalidName
