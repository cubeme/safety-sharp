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
open SafetySharp.Modeling
open SafetySharp.CSharpCompiler.Analyzers
open SafetySharp.CSharpCompiler.Roslyn.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols

[<TestFixture>]
module SS1004 =
    let getDiagnostic = TestCompilation.GetDiagnostic (SS1004 ())

    let ss1004 location memberName =
        Diagnostic ("SS1004", (1, location), (1, location + 1), 
            sprintf "'%s' must be marked with either '%s' or '%s'." memberName typeof<RequiredAttribute>.FullName typeof<ProvidedAttribute>.FullName)
        |> Some

    [<Test>]
    let ``Method or property without attributes is invalid`` () =
        getDiagnostic "interface C : IComponent { void M(); }" =? ss1004 32 "C.M()"
        getDiagnostic "interface C : IComponent { int M { get; set; }}" =? ss1004 31 "C.M"

    [<Test>]
    let ``Method or property with only one of the attributes is valid`` () =
        getDiagnostic "interface C : IComponent { [Required] void M(); }" =? None
        getDiagnostic "interface C : IComponent { [Required] int M { get; set; }}" =? None
        getDiagnostic "interface C : IComponent { [Provided] void M(); }" =? None
        getDiagnostic "interface C : IComponent { [Provided] int M { get; set; }}" =? None

    [<Test>]
    let ``Method or property with both attributes is valid`` () =
        getDiagnostic "interface C : IComponent { [Required, Provided] void M(); }" =? None
        getDiagnostic "interface C : IComponent { [Required, Provided] int M { get; set; }}" =? None
        getDiagnostic "interface C : IComponent { [Required] [Provided] void M(); }" =? None
        getDiagnostic "interface C : IComponent { [Required] [Provided] int M { get; set; }}" =? None

    [<Test>]
    let ``Method or property without attributes outside of component interface is valid`` () =
        getDiagnostic "interface C { void M(); }" =? None
        getDiagnostic "interface C { int M { get; set; }}" =? None
        getDiagnostic "class C : Component { void M() {} }" =? None
        getDiagnostic "class C : Component { int M { get; set; }}" =? None
        getDiagnostic "class C { void M() {} }" =? None
        getDiagnostic "class C { int M { get; set; }}" =? None
        getDiagnostic "class C : IComponent { public void Update() {} void M() {} }" =? None
        getDiagnostic "class C : IComponent { public void Update() {} int M { get; set; }}" =? None