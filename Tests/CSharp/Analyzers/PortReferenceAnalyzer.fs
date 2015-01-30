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
open SafetySharp.CSharp.Roslyn
open SafetySharp.CSharp.Roslyn.Syntax
open SafetySharp.CSharp.Roslyn.Symbols

[<TestFixture>]
module ``Referenced ports must exist`` =
    let getDiagnostic = TestCompilation.GetDiagnostic (PortReferenceAnalyzer ())

    let provUnknown location componentType portName =
        errorDiagnostic DiagnosticIdentifier.UnknownProvidedPort (1, location) (1, location + String.length portName)
            "'%s' does not declare a provided port named '%s'." componentType portName

    let reqUnknown location componentType portName =
        errorDiagnostic DiagnosticIdentifier.UnknownRequiredPort (1, location) (1, location + String.length portName)
            "'%s' does not declare a required port named '%s'." componentType portName

    let provInaccessible location componentType portName =
        errorDiagnostic DiagnosticIdentifier.InaccessibleProvidedPort (1, location) (1, location + String.length portName)
            "Provided port '%s.%s' is inaccessible due to its protection level." componentType portName

    let reqInaccessible location componentType portName =
        errorDiagnostic DiagnosticIdentifier.InaccessibleRequiredPort (1, location) (1, location + String.length portName)
            "Required port '%s.%s' is inaccessible due to its protection level." componentType portName

    [<Test>]
    let ``non-existent required port is invalid`` () =
        getDiagnostic "namespace Y { class X : Component { X() { var x = RequiredPorts.Xyz; } } }" =? reqUnknown 64 "Y.X" "Xyz"
        getDiagnostic "namespace Y { class X : Component { X() { var x = base.RequiredPorts.Xyz; } } }" =? reqUnknown 69 "Y.X" "Xyz"
        getDiagnostic "namespace Y { class X : Component { X() { var x = this.RequiredPorts.Xyz; } } }" =? reqUnknown 69 "Y.X" "Xyz"
        getDiagnostic "namespace Y { class X : Component { X(X x) { var y = x.RequiredPorts.Xyz; } } }" =? reqUnknown 69 "Y.X" "Xyz"
        getDiagnostic "namespace Y { class X : Component { X() { X x = null; var y = x.RequiredPorts.Xyz; } } }" =? reqUnknown 78 "Y.X" "Xyz"
        getDiagnostic "namespace Y { class X : Component { X x; X() { var y = x.RequiredPorts.Xyz; } } }" =? reqUnknown 71 "Y.X" "Xyz"
        getDiagnostic "namespace Y { class X : Component { X x { get; set; } X() { var y = x.RequiredPorts.Xyz; } } }" =? reqUnknown 84 "Y.X" "Xyz"
        getDiagnostic "namespace Y { class X : Component { X x() { return null; } X() { var y = x().RequiredPorts.Xyz; } } }" =? reqUnknown 91 "Y.X" "Xyz"
        getDiagnostic "class Y : Component { } class X : Component { extern void Xyz(); X(Y y) { var z = y.RequiredPorts.Xyz; } }" =? reqUnknown 98 "Y" "Xyz"
        getDiagnostic "class X : Component { X(Component y) { var z = y.RequiredPorts.Xyz; } }" =? reqUnknown 63 "SafetySharp.Modeling.Component" "Xyz"
        getDiagnostic "class X : Component { X(IComponent y) { var z = y.RequiredPorts.Xyz; } }" =? reqUnknown 64 "SafetySharp.Modeling.IComponent" "Xyz"
        getDiagnostic "interface I : IComponent {} class X : Component { extern void Xyz(); X(I y) { var z = y.RequiredPorts.Xyz; } }" =? reqUnknown 102 "I" "Xyz"

    [<Test>]
    let ``non-existent required port is invalid when provided port of same name exists`` () =
        getDiagnostic "class X : Component { void Xyz() {} X() { var x = RequiredPorts.Xyz; } }" =? reqUnknown 64 "X" "Xyz"
        getDiagnostic "interface I : IComponent { [Provided] void Xyz(); } class X : Component { X(I i) { var x = i.RequiredPorts.Xyz; } }" =? reqUnknown 107 "I" "Xyz"

    [<Test>]
    let ``inaccessible required port is invalid`` () =
        getDiagnostic "class Y : Component { extern void M(); } class X : Component { X(Y y) { var z = y.RequiredPorts.M; } }" =? reqInaccessible 96 "Y" "M"

    [<Test>]
    let ``uses accessible required port when inaccessible one of same name is also in scope`` () =
        getDiagnostic "class Y : Component { public extern void M(); } class Z : Y { extern void M(int i); } class X : Component { X(Z y) { var z = y.RequiredPorts.M; } }" =? None

    [<Test>]
    let ``non-existent provided port is invalid`` () =
        getDiagnostic "namespace Y { class X : Component { X() { var x = ProvidedPorts.Xyz; } } }" =? provUnknown 64 "Y.X" "Xyz"
        getDiagnostic "namespace Y { class X : Component { X() { var x = this.ProvidedPorts.Xyz; } } }" =? provUnknown 69 "Y.X" "Xyz"
        getDiagnostic "namespace Y { class X : Component { X() { var x = base.ProvidedPorts.Xyz; } } }" =? provUnknown 69 "Y.X" "Xyz"
        getDiagnostic "namespace Y { class X : Component { X(X x) { var y = x.ProvidedPorts.Xyz; } } }" =? provUnknown 69 "Y.X" "Xyz"
        getDiagnostic "namespace Y { class X : Component { X() { X x = null; var y = x.ProvidedPorts.Xyz; } } }" =? provUnknown 78 "Y.X" "Xyz"
        getDiagnostic "namespace Y { class X : Component { X x; X() { var y = x.ProvidedPorts.Xyz; } } }" =? provUnknown 71 "Y.X" "Xyz"
        getDiagnostic "namespace Y { class X : Component { X x { get; set; } X() { var y = x.ProvidedPorts.Xyz; } } }" =? provUnknown 84 "Y.X" "Xyz"
        getDiagnostic "namespace Y { class X : Component { X x() { return null; } X() { var y = x().ProvidedPorts.Xyz; } } }" =? provUnknown 91 "Y.X" "Xyz"
        getDiagnostic "class Y : Component { } class X : Component { void Xyz() {} X(Y y) { var z = y.ProvidedPorts.Xyz; } }" =? provUnknown 93 "Y" "Xyz"
        getDiagnostic "class X : Component { X(Component y) { var z = y.ProvidedPorts.Xyz; } }" =? provUnknown 63 "SafetySharp.Modeling.Component" "Xyz"
        getDiagnostic "class X : Component { X(IComponent y) { var z = y.ProvidedPorts.Xyz; } }" =? provUnknown 64 "SafetySharp.Modeling.IComponent" "Xyz"
        getDiagnostic "interface I : IComponent {} class X : Component { void Xyz() {} X(I y) { var z = y.ProvidedPorts.Xyz; } }" =? provUnknown 97 "I" "Xyz"

    [<Test>]
    let ``non-existent provided port is invalid when required port of same name exists`` () =
        getDiagnostic "class X : Component { extern void Xyz(); X() { var x = ProvidedPorts.Xyz; } }" =? provUnknown 69 "X" "Xyz"
        getDiagnostic "interface I : IComponent { [Required] void Xyz(); } class X : Component { X(I i) { var x = i.ProvidedPorts.Xyz; } }" =? provUnknown 107 "I" "Xyz"

    [<Test>]
    let ``inaccessible provided port is invalid`` () =
        getDiagnostic "class Y : Component { void M() {} } class X : Component { X(Y y) { var z = y.ProvidedPorts.M; } }" =? provInaccessible 91 "Y" "M"

    [<Test>]
    let ``uses accessible provided port when inaccessible one of same name is also in scope`` () =
        getDiagnostic "class Y : Component { public void M() {} } class Z : Y { void M(int i) {} } class X : Component { X(Z y) { var z = y.ProvidedPorts.M; } }" =? None

    [<Test>]
    let ``existing required port is valid`` () =
        getDiagnostic "namespace Y { class X : Component { extern void Xyz(); X() { var x = RequiredPorts.Xyz; } } }" =? None
        getDiagnostic "namespace Y { class X : Component { extern void Xyz(); X() { var x = base.RequiredPorts.Xyz; } } }" =? None
        getDiagnostic "namespace Y { class X : Component { extern void Xyz(); X() { var x = this.RequiredPorts.Xyz; } } }" =? None
        getDiagnostic "namespace Y { class X : Component { extern void Xyz(); X(X x) { var y = x.RequiredPorts.Xyz; } } }" =? None
        getDiagnostic "namespace Y { class X : Component { extern void Xyz(); X() { X x = null; var y = x.RequiredPorts.Xyz; } } }" =? None
        getDiagnostic "namespace Y { class X : Component { extern void Xyz(); X x; X() { var y = x.RequiredPorts.Xyz; } } }" =? None
        getDiagnostic "namespace Y { class X : Component { extern void Xyz(); X x { get; set; } X() { var y = x.RequiredPorts.Xyz; } } }" =? None
        getDiagnostic "namespace Y { class X : Component { extern void Xyz(); X x() { return null; } X() { var y = x().RequiredPorts.Xyz; } } }" =? None
        getDiagnostic "class Y : Component { public extern void Xyz(); } class X : Component { X(Y y) { var z = y.RequiredPorts.Xyz; } }" =? None
        getDiagnostic "interface I : IComponent { [Required] void Xyz(); } class X : Component { X(I y) { var z = y.RequiredPorts.Xyz; } }" =? None

    [<Test>]
    let ``existing provided port is valid`` () =
        getDiagnostic "namespace Y { class X : Component { void Xyz() {} X() { var x = ProvidedPorts.Xyz; } } }" =? None
        getDiagnostic "namespace Y { class X : Component { void Xyz() {} X() { var x = this.ProvidedPorts.Xyz; } } }" =? None
        getDiagnostic "namespace Y { class X : Component { void Xyz() {} X() { var x = base.ProvidedPorts.Xyz; } } }" =? None
        getDiagnostic "namespace Y { class X : Component { void Xyz() {} X(X x) { var y = x.ProvidedPorts.Xyz; } } }" =? None
        getDiagnostic "namespace Y { class X : Component { void Xyz() {} X() { X x = null; var y = x.ProvidedPorts.Xyz; } } }" =? None
        getDiagnostic "namespace Y { class X : Component { void Xyz() {} X x; X() { var y = x.ProvidedPorts.Xyz; } } }" =? None
        getDiagnostic "namespace Y { class X : Component { void Xyz() {} X x { get; set; } X() { var y = x.ProvidedPorts.Xyz; } } }" =? None
        getDiagnostic "namespace Y { class X : Component { void Xyz() {} X x() { return null; } X() { var y = x().ProvidedPorts.Xyz; } } }" =? None
        getDiagnostic "class Y : Component { public void Xyz() {} } class X : Component { X(Y y) { var z = y.ProvidedPorts.Xyz; } }" =? None
        getDiagnostic "interface I : IComponent { [Provided] void Xyz(); } class X : Component { X(I y) { var z = y.ProvidedPorts.Xyz; } }" =? None

    [<Test>]
    let ``considers inherited ports`` () =
        getDiagnostic "class Y : Component { protected extern void M(); } class X : Y { X() { var y = RequiredPorts.M; } }" =? None
        getDiagnostic "class Y : Component { protected void M() {} } class X : Y { X() { var y = ProvidedPorts.M; } }" =? None
        getDiagnostic "interface J : I {} interface I : IComponent { [Required] void M(); } class X : Component { X(J j) { var y = j.RequiredPorts.M; } }" =? None
        getDiagnostic "interface J : I {} interface I : IComponent { [Provided] void M(); } class X : Component { X(J j) { var y = j.ProvidedPorts.M; } }" =? None

    [<Test>]
    let ``does not consider ports of derived types`` () =
        getDiagnostic "class Y : X { extern void M(); } class X : Component { public X() { var y = RequiredPorts.M; } }" =? reqUnknown 90 "X" "M"
        getDiagnostic "class Y : X { void M() {} } class X : Component { public X() { var y = ProvidedPorts.M; } }" =? provUnknown 85 "X" "M"
        getDiagnostic "interface J : IComponent {} interface I : J { [Required] void M(); } class X : Component { public X(J j) { var y = j.RequiredPorts.M; } }" =? reqUnknown 131 "J" "M"
        getDiagnostic "interface J : IComponent {} interface I : J { [Provided] void M(); } class X : Component { public X(J j) { var y = j.ProvidedPorts.M; } }" =? provUnknown 131 "J" "M"