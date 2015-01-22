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
open SafetySharp.CSharp.Analyzers
open SafetySharp.CSharp.Roslyn.Syntax
open SafetySharp.CSharp.Roslyn.Symbols

[<TestFixture>]
module SS1002 =
    let getDiagnostic = TestCompilation.GetDiagnostic (SS1002 ())

    let ss1002 location memberName =
        Diagnostic ("SS1002", (1, location), (1, location + 1), sprintf "Provided port '%s' cannot be extern." memberName)
        |> Some

    [<Test>]
    let ``Method or property without attributes is valid`` () =
        getDiagnostic "class C : Component { void M() {}}" =? None
        getDiagnostic "class C : Component { int M { get; set; }}" =? None
        getDiagnostic "class C : Component { extern void M(); }" =? None
        getDiagnostic "class C : Component { extern int M { get; set; }}" =? None

    [<Test>]
    let ``Non-extern method or property with Provided attribute is valid`` () =
        getDiagnostic "class C : Component { [Provided] void M() {}}" =? None
        getDiagnostic "class C : Component { [Provided] int M { get; set; }}" =? None

    [<Test>]
    let ``Extern method or property with Provided attribute is invalid`` () =
        getDiagnostic "class C : Component { [Provided] extern void M();}" =? ss1002 45 "C.M()"
        getDiagnostic "class C : Component { [Provided] extern int M { get; set; }}" =? ss1002 44 "C.M"

    [<Test>]
    let ``Extern method or property with Provided attribute outside of component classes is valid`` () =
        getDiagnostic "class C { [Provided] extern void M();}" =? None
        getDiagnostic "class C { [Provided] extern int M { get; set; }}" =? None