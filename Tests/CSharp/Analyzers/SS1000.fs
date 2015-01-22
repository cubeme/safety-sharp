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
open SafetySharp.CSharpCompiler.Analyzers
open SafetySharp.CSharpCompiler.Roslyn.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols

[<TestFixture>]
module SS1000 =
    let getDiagnostic = TestCompilation.GetDiagnostic (SS1000 ())

    let ss1000 location memberName =
        Diagnostic ("SS1000", (1, location), (1, location + 1), 
            sprintf "'%s' cannot be marked with both '%s' and '%s'." memberName typeof<RequiredAttribute>.FullName typeof<ProvidedAttribute>.FullName)
        |> Some

    [<Test>]
    let ``Method or property without attributes is valid`` () =
        getDiagnostic "class C : Component { void M() {}}" =? None
        getDiagnostic "class C : Component { int M { get; set; }}" =? None
        getDiagnostic "interface C : IComponent { void M(); }" =? None
        getDiagnostic "interface C : IComponent { int M { get; set; }}" =? None

    [<Test>]
    let ``Method or property with only one of the attributes is valid`` () =
        getDiagnostic "class C : Component { [Required] void M() {}}" =? None
        getDiagnostic "class C : Component { [Required] int M { get; set; }}" =? None
        getDiagnostic "class C : Component { [Provided] void M() {}}" =? None
        getDiagnostic "class C : Component { [Provided] int M { get; set; }}" =? None
        getDiagnostic "interface C : IComponent { [Required] void M(); }" =? None
        getDiagnostic "interface C : IComponent { [Required] int M { get; set; }}" =? None
        getDiagnostic "interface C : IComponent { [Provided] void M(); }" =? None
        getDiagnostic "interface C : IComponent { [Provided] int M { get; set; }}" =? None

    [<Test>]
    let ``Method or property with both attributes is invalid`` () =
        getDiagnostic "class C : Component { [Required, Provided] void M() {}}" =? ss1000 48 "C.M()"
        getDiagnostic "class C : Component { [Required, Provided] int M { get; set; }}" =? ss1000 47 "C.M"
        getDiagnostic "class C : Component { [Required] [Provided] void M() {}}" =? ss1000 49 "C.M()"
        getDiagnostic "class C : Component { [Required] [Provided] int M { get; set; }}" =? ss1000 48 "C.M"
        getDiagnostic "interface C : IComponent { [Required, Provided] void M(); }" =? ss1000 53 "C.M()"
        getDiagnostic "interface C : IComponent { [Required, Provided] int M { get; set; }}" =? ss1000 52 "C.M"
        getDiagnostic "interface C : IComponent { [Required] [Provided] void M(); }" =? ss1000 54 "C.M()"
        getDiagnostic "interface C : IComponent { [Required] [Provided] int M { get; set; }}" =? ss1000 53 "C.M"

    [<Test>]
    let ``Method or property with both attributes outside of component class or interface is valid`` () =
        getDiagnostic "class C { [Required, Provided] void M() {}}" =? None
        getDiagnostic "class C { [Required, Provided] int M { get; set; }}" =? None
        getDiagnostic "class C { [Required] [Provided] void M() {}}" =? None
        getDiagnostic "class C { [Required] [Provided] int M { get; set; }}" =? None
        getDiagnostic "interface C { [Required, Provided] void M(); }" =? None
        getDiagnostic "interface C { [Required, Provided] int M { get; set; }}" =? None
        getDiagnostic "interface C { [Required] [Provided] void M(); }" =? None
        getDiagnostic "interface C { [Required] [Provided] int M { get; set; }}" =? None