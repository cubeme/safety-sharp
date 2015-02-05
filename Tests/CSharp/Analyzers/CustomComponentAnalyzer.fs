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
module ``Custom implementation of IComponent interface`` =
    let getDiagnostic = TestCompilation.GetDiagnostic (CustomComponentAnalyzer ())
    let implementation = "public void Update() {} public dynamic RequiredPorts { get { return null; } } public dynamic ProvidedPorts { get { return null; } }"

    let custom typeName location =
        errorDiagnostic DiagnosticIdentifier.CustomComponent (1, location) (1, location + 1) 
            "Class '%s' cannot implement 'SafetySharp.Modeling.IComponent' explicitly; derive from 'SafetySharp.Modeling.Component' instead." typeName

    let reimplementation typeName location =
        errorDiagnostic DiagnosticIdentifier.ComponentInterfaceReimplementation (1, location) (1, location + 1) 
            "Class '%s' cannot reimplement 'SafetySharp.Modeling.IComponent'." typeName

    [<Test>]
    let ``type derived from Component is valid`` () =
        getDiagnostic "class X : Component {}" =? None

    [<Test>]
    let ``nested type derived from Component is valid`` () =
        getDiagnostic "class Y { class X : Component {}}" =? None
        getDiagnostic "class Y : Component { class X : Component {}}" =? None

    [<Test>]
    let ``type indirectly derived from Component is valid`` () =
        getDiagnostic "class Y : Component {} class X : Y {}" =? None

    [<Test>]
    let ``type derived from Component is invalid when IComponent is reimplemented`` () =
        getDiagnostic "class X : Component, IComponent {}" =? reimplementation "X" 6

    [<Test>]
    let ``type indirectly derived from Component is invalid when IComponent is reimplemented`` () =
        getDiagnostic "class Y : Component {} class X : Y, IComponent {}" =? reimplementation "X" 29

    [<Test>]
    let ``base type not derived from Component is invalid`` () =
        getDiagnostic (sprintf "class X : IComponent { %s }" implementation) =? custom "X" 6

    [<Test>]
    let ``nested base type not derived from Component is invalid`` () =
        getDiagnostic (sprintf "class Y { class X : IComponent { %s }}" implementation) =? custom "Y.X" 16
        getDiagnostic (sprintf "class Y : Component { class X : IComponent { %s }}" implementation) =? custom "Y.X" 28

    [<Test>]
    let ``inherited type not derived from Component is invalid`` () =
        getDiagnostic (sprintf "class Y {} class X : IComponent { %s }" implementation) =? custom "X" 17