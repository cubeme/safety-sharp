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
module ``Marked with both provided and required port attribute`` =
    let getDiagnostic = TestCompilation.GetDiagnostic (PortKindAnalyzer ())

    let ambiguous location memberName =
        createDiagnostic DiagnosticIdentifier.AmbiguousPortKind (1, location) (1, location + 1)
            "'%s' cannot be marked with both '%s' and '%s'." memberName typeof<RequiredAttribute>.FullName typeof<ProvidedAttribute>.FullName

    [<Test>]
    let ``Method or property without attributes is valid`` () =
        getDiagnostic "class C : Component { void M() {}}" =? None
        getDiagnostic "class C : Component { int M { get; set; }}" =? None
        getDiagnostic "interface C : IComponent { void M(); }" =? None
        getDiagnostic "interface C : IComponent { int M { get; set; }}" =? None

    [<Test>]
    let ``Method or property with only one of the attributes is valid`` () =
        getDiagnostic "class C : Component { [Required] extern void M(); }" =? None
        getDiagnostic "class C : Component { [Required] extern int M { get; set; }}" =? None
        getDiagnostic "class C : Component { [Provided] void M() {}}" =? None
        getDiagnostic "class C : Component { [Provided] int M { get; set; }}" =? None
        getDiagnostic "interface C : IComponent { [Required] void M(); }" =? None
        getDiagnostic "interface C : IComponent { [Required] int M { get; set; }}" =? None
        getDiagnostic "interface C : IComponent { [Provided] void M(); }" =? None
        getDiagnostic "interface C : IComponent { [Provided] int M { get; set; }}" =? None

    [<Test>]
    let ``Method or property with both attributes is invalid`` () =
        getDiagnostic "class C : Component { [Required, Provided] void M() {}}" =? ambiguous 48 "C.M()"
        getDiagnostic "class C : Component { [Required, Provided] int M { get; set; }}" =? ambiguous 47 "C.M"
        getDiagnostic "class C : Component { [Required] [Provided] void M() {}}" =? ambiguous 49 "C.M()"
        getDiagnostic "class C : Component { [Required] [Provided] int M { get; set; }}" =? ambiguous 48 "C.M"
        getDiagnostic "interface C : IComponent { [Required, Provided] void M(); }" =? ambiguous 53 "C.M()"
        getDiagnostic "interface C : IComponent { [Required, Provided] int M { get; set; }}" =? ambiguous 52 "C.M"
        getDiagnostic "interface C : IComponent { [Required] [Provided] void M(); }" =? ambiguous 54 "C.M()"
        getDiagnostic "interface C : IComponent { [Required] [Provided] int M { get; set; }}" =? ambiguous 53 "C.M"

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

[<TestFixture>]
module ``Provided ports cannot be extern`` =
    let getDiagnostic = TestCompilation.GetDiagnostic (PortKindAnalyzer ())

    let prov location memberName =
        createDiagnostic DiagnosticIdentifier.ExternProvidedPort (1, location) (1, location + 1)
            "Provided port '%s' cannot be extern." memberName

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
        getDiagnostic "class C : Component { [Provided] extern void M();}" =? prov 45 "C.M()"
        getDiagnostic "class C : Component { [Provided] extern int M { get; set; }}" =? prov 44 "C.M"

    [<Test>]
    let ``Extern method or property with Provided attribute outside of component classes is valid`` () =
        getDiagnostic "class C { [Provided] extern void M();}" =? None
        getDiagnostic "class C { [Provided] extern int M { get; set; }}" =? None

[<TestFixture>]
module ``Required ports cannot be non extern`` =
    let getDiagnostic = TestCompilation.GetDiagnostic (PortKindAnalyzer ())

    let req location memberName =
        createDiagnostic DiagnosticIdentifier.NonExternRequiredPort (1, location) (1, location + 1) 
            "Required port '%s' must be extern." memberName

    [<Test>]
    let ``Method or property without attributes is valid`` () =
        getDiagnostic "class C : Component { void M() {}}" =? None
        getDiagnostic "class C : Component { int M { get; set; }}" =? None
        getDiagnostic "class C : Component { extern void M(); }" =? None
        getDiagnostic "class C : Component { extern int M { get; set; }}" =? None

    [<Test>]
    let ``Non-extern method or property with Required attribute is invalid`` () =
        getDiagnostic "class C : Component { [Required] void M() {}}" =? req 38 "C.M()"
        getDiagnostic "class C : Component { [Required] int M { get; set; }}" =? req 37 "C.M"

    [<Test>]
    let ``Extern method or property with Required attribute is valid`` () =
        getDiagnostic "class C : Component { [Required] extern void M();}" =? None
        getDiagnostic "class C : Component { [Required] extern int M { get; set; }}" =? None

    [<Test>]
    let ``Non-extern method or property with Required attribute outside of component classes is valid`` () =
        getDiagnostic "class C { [Provided] void M() {}}" =? None
        getDiagnostic "class C { [Provided] int M { get; set; }}" =? None