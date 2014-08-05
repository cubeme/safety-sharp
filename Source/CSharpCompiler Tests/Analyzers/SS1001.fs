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
module SS1001 =
    let getDiagnostic = TestCompilation.GetDiagnostic (SS1001 ())

    let ss1001 location memberName =
        Diagnostic ("SS1001", (1, location), (1, location + 3), 
            sprintf "'%s' cannot be marked with either '%s' or '%s'." memberName typeof<RequiredAttribute>.FullName typeof<ProvidedAttribute>.FullName)
        |> Some

    [<Test>]
    let ``Accessors without attributes are valid`` () =
        getDiagnostic "class C : Component { int M { get; set; }}" =? None
        getDiagnostic "interface C : IComponent { int M { get; set; }}" =? None

    [<Test>]
    let ``Accessors with single attribute are invalid`` () =
        getDiagnostic "class C : Component { int M { [Required] get; set; }}" =? ss1001 41 "C.M.get"
        getDiagnostic "class C : Component { int M { [Provided] get; set; }}" =? ss1001 41 "C.M.get"
        getDiagnostic "class C : Component { int M { get; [Required] set; }}" =? ss1001 46 "C.M.set"
        getDiagnostic "class C : Component { int M { get; [Provided] set; }}" =? ss1001 46 "C.M.set"
        getDiagnostic "interface C : IComponent { int M { [Required] get; set; }}" =? ss1001 46 "C.M.get"
        getDiagnostic "interface C : IComponent { int M { [Provided] get; set; }}" =? ss1001 46 "C.M.get"
        getDiagnostic "interface C : IComponent { int M { get; [Required] set; }}" =? ss1001 51 "C.M.set"
        getDiagnostic "interface C : IComponent { int M { get; [Provided] set; }}" =? ss1001 51 "C.M.set"

    [<Test>]
    let ``Accessors with both attributes are invalid`` () =
        getDiagnostic "class C : Component { int M { [Required, Provided] get; set; }}" =? ss1001 51 "C.M.get"
        getDiagnostic "class C : Component { int M { [Required] [Provided] get; set; }}" =? ss1001 52 "C.M.get"
        getDiagnostic "class C : Component { int M { get; [Required, Provided] set; }}" =? ss1001 56 "C.M.set"
        getDiagnostic "class C : Component { int M { get; [Required] [Provided] set; }}" =? ss1001 57 "C.M.set"
        getDiagnostic "interface C : IComponent { int M { [Required, Provided] get; set; }}" =? ss1001 56 "C.M.get"
        getDiagnostic "interface C : IComponent { int M { [Required] [Provided] get; set; }}" =? ss1001 57 "C.M.get"
        getDiagnostic "interface C : IComponent { int M { get; [Required, Provided] set; }}" =? ss1001 61 "C.M.set"
        getDiagnostic "interface C : IComponent { int M { get; [Required] [Provided] set; }}" =? ss1001 62 "C.M.set"

    [<Test>]
    let ``Accessors with attributes outside of component class or interface are valid`` () =
        getDiagnostic "class C { int M { [Required, Provided] get; set; }}" =? None
        getDiagnostic "class C { int M { get; [Provided] set; }}" =? None
        getDiagnostic "interface C { int M { get; [Required] set; }}" =? None
        getDiagnostic "interface C { int M { [Provided] get; set; }}" =? None