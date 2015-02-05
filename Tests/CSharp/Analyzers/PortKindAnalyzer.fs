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
module ``Port kinds`` =
    let getDiagnostic = TestCompilation.GetDiagnostic (PortKindAnalyzer ())

    let ambiguous location memberName =
        errorDiagnostic DiagnosticIdentifier.AmbiguousPortKind (1, location) (1, location + 1)
            "'%s' cannot be marked with both '%s' and '%s'." memberName typeof<RequiredAttribute>.FullName typeof<ProvidedAttribute>.FullName

    let prov location memberName =
        errorDiagnostic DiagnosticIdentifier.ExternProvidedPort (1, location) (1, location + 1)
            "Provided port '%s' cannot be extern." memberName

    let req location memberName =
        errorDiagnostic DiagnosticIdentifier.NonExternRequiredPort (1, location) (1, location + 1) 
            "Required port '%s' must be extern." memberName

    let updateport location memberName =
        errorDiagnostic DiagnosticIdentifier.UpdateMethodMarkedAsPort (1, location) (1, location + 6) 
            "'%s' overrides 'SafetySharp.Modeling.Component.Update()' and is therefore not a port. The method cannot \
             be marked with 'SafetySharp.Modeling.ProvidedAttribute' or 'SafetySharp.Modeling.RequiredAttribute'." memberName

    let isExtern location memberName =
        errorDiagnostic DiagnosticIdentifier.ExternUpdateMethod (1, location) (1, location + 6) 
            "'%s' cannot be extern as it overrides 'SafetySharp.Modeling.Component.Update()'." memberName

    let accessor location memberName =
        errorDiagnostic DiagnosticIdentifier.PortPropertyAccessor (1, location) (1, location + 3)
            "'%s' cannot be marked with either '%s' or '%s'." memberName typeof<RequiredAttribute>.FullName typeof<ProvidedAttribute>.FullName

    let interfacePort location memberName =
        errorDiagnostic DiagnosticIdentifier.UnmarkedInterfacePort (1, location) (1, location + 1)
            "'%s' must be marked with either '%s' or '%s'." memberName typeof<RequiredAttribute>.FullName typeof<ProvidedAttribute>.FullName

    [<Test>]
    let ``method or property without attributes is valid`` () =
        getDiagnostic "class C : Component { void M() {}}" =? None
        getDiagnostic "class C : Component { int M { get; set; }}" =? None
        getDiagnostic "class C : Component { extern void M(); }" =? None
        getDiagnostic "class C : Component { extern int M { get; set; }}" =? None

    [<Test>]
    let ``method or property with only one of the attributes is valid`` () =
        getDiagnostic "class C : Component { [Required] extern void M(); }" =? None
        getDiagnostic "class C : Component { [Required] extern int M { get; set; }}" =? None
        getDiagnostic "class C : Component { [Provided] void M() {}}" =? None
        getDiagnostic "class C : Component { [Provided] int M { get; set; }}" =? None
        getDiagnostic "interface C : IComponent { [Required] void M(); }" =? None
        getDiagnostic "interface C : IComponent { [Required] int M { get; set; }}" =? None
        getDiagnostic "interface C : IComponent { [Provided] void M(); }" =? None
        getDiagnostic "interface C : IComponent { [Provided] int M { get; set; }}" =? None

    [<Test>]
    let ``method or property with both attributes is invalid`` () =
        getDiagnostic "class C : Component { [Required, Provided] void M() {}}" =? ambiguous 48 "C.M()"
        getDiagnostic "class C : Component { [Required, Provided] int M { get; set; }}" =? ambiguous 47 "C.M"
        getDiagnostic "class C : Component { [Required] [Provided] void M() {}}" =? ambiguous 49 "C.M()"
        getDiagnostic "class C : Component { [Required] [Provided] int M { get; set; }}" =? ambiguous 48 "C.M"
        getDiagnostic "interface C : IComponent { [Required, Provided] void M(); }" =? ambiguous 53 "C.M()"
        getDiagnostic "interface C : IComponent { [Required, Provided] int M { get; set; }}" =? ambiguous 52 "C.M"
        getDiagnostic "interface C : IComponent { [Required] [Provided] void M(); }" =? ambiguous 54 "C.M()"
        getDiagnostic "interface C : IComponent { [Required] [Provided] int M { get; set; }}" =? ambiguous 53 "C.M"

    [<Test>]
    let ``method or property with both attributes outside of component class or interface is valid`` () =
        getDiagnostic "class C { [Required, Provided] void M() {}}" =? None
        getDiagnostic "class C { [Required, Provided] int M { get; set; }}" =? None
        getDiagnostic "class C { [Required] [Provided] void M() {}}" =? None
        getDiagnostic "class C { [Required] [Provided] int M { get; set; }}" =? None
        getDiagnostic "interface C { [Required, Provided] void M(); }" =? None
        getDiagnostic "interface C { [Required, Provided] int M { get; set; }}" =? None
        getDiagnostic "interface C { [Required] [Provided] void M(); }" =? None
        getDiagnostic "interface C { [Required] [Provided] int M { get; set; }}" =? None

    [<Test>]
    let ``non-extern method or property with Provided attribute is valid`` () =
        getDiagnostic "class C : Component { [Provided] void M() {}}" =? None
        getDiagnostic "class C : Component { [Provided] int M { get; set; }}" =? None

    [<Test>]
    let ``extern method or property with Provided attribute is invalid`` () =
        getDiagnostic "class C : Component { [Provided] extern void M();}" =? prov 45 "C.M()"
        getDiagnostic "class C : Component { [Provided] extern int M { get; set; }}" =? prov 44 "C.M"

    [<Test>]
    let ``extern method or property with Provided attribute outside of component classes is valid`` () =
        getDiagnostic "class C { [Provided] extern void M();}" =? None
        getDiagnostic "class C { [Provided] extern int M { get; set; }}" =? None

    [<Test>]
    let ``non-extern method or property with Required attribute is invalid`` () =
        getDiagnostic "class C : Component { [Required] void M() {}}" =? req 38 "C.M()"
        getDiagnostic "class C : Component { [Required] int M { get; set; }}" =? req 37 "C.M"

    [<Test>]
    let ``extern method or property with Required attribute is valid`` () =
        getDiagnostic "class C : Component { [Required] extern void M();}" =? None
        getDiagnostic "class C : Component { [Required] extern int M { get; set; }}" =? None

    [<Test>]
    let ``non-extern method or property with Required attribute outside of component classes is valid`` () =
        getDiagnostic "class C { [Provided] void M() {}}" =? None
        getDiagnostic "class C { [Provided] int M { get; set; }}" =? None

    [<Test>]
    let ``unmarked update method is valid`` () =
        getDiagnostic "class C : Component { public override void Update() {} }" =? None

    [<Test>]
    let ``replaced update method is valid`` () =
        getDiagnostic "class C : Component { [Provided] public new void Update() {} }" =? None
        getDiagnostic "class C : Component { [Required] public new extern void Update(); }" =? None

    [<Test>]
    let ``unmarked inherited update method is valid`` () =
        getDiagnostic "class C : Component { public override void Update() {}} class D : C { public override void Update() {} }" =? None

    [<Test>]
    let ``update method marked as required port is invalid`` () =
        getDiagnostic "class C : Component { [Required] public override void Update() {} }" =? updateport 54 "C.Update()"

    [<Test>]
    let ``update method marked as provided port is invalid`` () =
        getDiagnostic "class C : Component { [Provided] public override void Update() {} }" =? updateport 54 "C.Update()"

    [<Test>]
    let ``update method marked with both port attributes is invalid`` () =
        getDiagnostic "class C : Component { [Provided, Required] public override void Update() {} }" =? updateport 64 "C.Update()"

    [<Test>]
    let ``extern update method is invalid`` () =
        getDiagnostic "class C : Component { public extern override void Update(); }" =? isExtern 50 "C.Update()"

    [<Test>]
    let ``extern replaced update method is invalid`` () =
        getDiagnostic "class C : Component { public extern new void Update(); }" =? None

    [<Test>]
    let ``accessors without attributes are valid`` () =
        getDiagnostic "class C : Component { int M { get; set; }}" =? None
        getDiagnostic "interface C : IComponent { [Provided] int M { get; set; }}" =? None
        getDiagnostic "class C : Component { extern int M { get; set; }}" =? None
        getDiagnostic "interface C : IComponent { [Required] int M { get; set; }}" =? None

    [<Test>]
    let ``accessors with single attribute are invalid`` () =
        getDiagnostic "class C : Component { int M { [Required] get; set; }}" =? accessor 41 "C.M.get"
        getDiagnostic "class C : Component { int M { [Provided] get; set; }}" =? accessor 41 "C.M.get"
        getDiagnostic "class C : Component { int M { get; [Required] set; }}" =? accessor 46 "C.M.set"
        getDiagnostic "class C : Component { int M { get; [Provided] set; }}" =? accessor 46 "C.M.set"
        getDiagnostic "interface C : IComponent { [Required] int M { [Required] get; set; }}" =? accessor 57 "C.M.get"
        getDiagnostic "interface C : IComponent { [Provided] int M { [Provided] get; set; }}" =? accessor 57 "C.M.get"
        getDiagnostic "interface C : IComponent { [Required] int M { get; [Required] set; }}" =? accessor 62 "C.M.set"
        getDiagnostic "interface C : IComponent { [Provided] int M { get; [Provided] set; }}" =? accessor 62 "C.M.set"

    [<Test>]
    let ``accessors with both attributes are invalid`` () =
        getDiagnostic "class C : Component { int M { [Required, Provided] get; set; }}" =? accessor 51 "C.M.get"
        getDiagnostic "class C : Component { int M { [Required] [Provided] get; set; }}" =? accessor 52 "C.M.get"
        getDiagnostic "class C : Component { int M { get; [Required, Provided] set; }}" =? accessor 56 "C.M.set"
        getDiagnostic "class C : Component { int M { get; [Required] [Provided] set; }}" =? accessor 57 "C.M.set"
        getDiagnostic "interface C : IComponent { [Required] int M { [Required, Provided] get; set; }}" =? accessor 67 "C.M.get"
        getDiagnostic "interface C : IComponent { [Required] int M { [Required] [Provided] get; set; }}" =? accessor 68 "C.M.get"
        getDiagnostic "interface C : IComponent { [Required] int M { get; [Required, Provided] set; }}" =? accessor 72 "C.M.set"
        getDiagnostic "interface C : IComponent { [Required] int M { get; [Required] [Provided] set; }}" =? accessor 73 "C.M.set"

    [<Test>]
    let ``accessors with attributes outside of component class or interface are valid`` () =
        getDiagnostic "class C { int M { [Required, Provided] get; set; }}" =? None
        getDiagnostic "class C { int M { get; [Provided] set; }}" =? None
        getDiagnostic "interface C { int M { get; [Required] set; }}" =? None
        getDiagnostic "interface C { int M { [Provided] get; set; }}" =? None

    [<Test>]
    let ``method or property without attributes is invalid`` () =
        getDiagnostic "interface C : IComponent { void M(); }" =? interfacePort 32 "C.M()"
        getDiagnostic "interface C : IComponent { int M { get; set; }}" =? interfacePort 31 "C.M"

    [<Test>]
    let ``method or property without attributes outside of component interface is valid`` () =
        getDiagnostic "interface C { void M(); }" =? None
        getDiagnostic "interface C { int M { get; set; }}" =? None
        getDiagnostic "class C : Component { void M() {} }" =? None
        getDiagnostic "class C : Component { int M { get; set; }}" =? None
        getDiagnostic "class C { void M() {} }" =? None
        getDiagnostic "class C { int M { get; set; }}" =? None
        getDiagnostic "class C : IComponent { public void Update() {} public dynamic RequiredPorts { get { return null; }} public dynamic ProvidedPorts { get { return null; }} void M() {} }" =? None
        getDiagnostic "class C : IComponent { public void Update() {} public dynamic RequiredPorts { get { return null; }} public dynamic ProvidedPorts { get { return null; }} int M { get; set; }}" =? None