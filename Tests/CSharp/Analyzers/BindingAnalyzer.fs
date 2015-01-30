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
module ``Binding validity`` =
    let getDiagnostic = TestCompilation.GetDiagnostic (BindingAnalyzer ())

    let assignment location length =
        errorDiagnostic DiagnosticIdentifier.ExpectedPortAssignment (1, location) (1, location + length)
            "A port assignment of the form 'component1.RequiredPorts.Port = component2.ProvidedPorts.Port' \
		    is required to initialize an instance of '%s'." typeof<PortBinding>.FullName

    let cast location length =
        errorDiagnostic DiagnosticIdentifier.ExpectedPortDelegateCast (1, location) (1, location + length)
            "Expected port to be cast to a delegate type."

    let reference location length =
        errorDiagnostic DiagnosticIdentifier.ExpectedPortReference (1, location) (1, location + length)
            "Expected a reference to a port of the form 'RequiredPorts.Port' or 'ProvidedPorts.Port'."

    let portList ports =
        if ports = [] then "<none>"
        else String.Join ("\n", ports |> Seq.map (sprintf "'%s'"))

    let ambiguous locationStart locationEnd leftPorts rightPorts =
        errorDiagnostic DiagnosticIdentifier.AmbiguousBinding (1, locationStart) (1, locationEnd)
            "Port binding is ambiguous: There are multiple accessible and signature-compatible ports \
			that could be bound. You can disambiguate the binding by explicitly casting one of the ports to a \
			delegate type with the signature of the port you intend to use. For instance, use 'RequiredPorts.X = \
			(Action<int>)ProvidedPorts.Y' if the port you want to bind is signature-compatible to the 'System.Action<int>' \
			delegate.\nCandidate ports for the left-hand side:\n%s\nCandidate ports for the right-hand side:\n%s" (portList leftPorts) (portList rightPorts)

    let failure locationStart locationEnd leftPorts rightPorts =
        errorDiagnostic DiagnosticIdentifier.BindingFailure (1, locationStart) (1, locationEnd)
            "There are no accessible signature-compatible ports that could be bound. \
		    \nCandidate ports for the left-hand side:\n%s\nCandidate ports for the right-hand side:\n%s" (portList leftPorts) (portList rightPorts)

    [<Test>]
    let ``non-failing unambiguous binding with single candidate is valid`` () =
        getDiagnostic "class X : Component { void M() {} extern void N(); X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M() {} extern void N(); X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); } }" =? None

    [<Test>]
    let ``non-failing unambiguous binding with multiple candidates is valid`` () =
        getDiagnostic "class X : Component { void M() {} extern void N(); extern void N(int i); X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M() {} void M(int i) {} extern void N(); X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M(int i) {} extern void N(); extern void N(int i); X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M() {} void M(int i) {} extern void N(int i); X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M() {} void M(bool b) {} extern void N(); extern void N(int i); X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M() {} void M(int i) {} extern void N(); extern void N(bool b); X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M() {} void M(ref bool b) {} extern void N(ref bool b); extern void N(int i); X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M(ref int i) {} void M(int i) {} extern void N(); extern void N(ref int i); X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); } }" =? None

    [<Test>]
    let ``binding where either side yields no ports is valid`` () =
        getDiagnostic "class X : Component { extern void N(); X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { extern void N(); X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M() {} X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M() {} X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); } }" =? None

    [<Test>]
    let ``bind invocation without port assignment is invalid`` () =
        getDiagnostic "class X : Component { X() { BindInstantaneous(null); } }" =? assignment 46 4
        getDiagnostic "class X : Component { X(PortBinding p) { BindInstantaneous(p); } }" =? assignment 59 1
        getDiagnostic "class X : Component { X() { BindDelayed(null); } }" =? assignment 40 4
        getDiagnostic "class X : Component { X(PortBinding p) { BindDelayed(p); } }" =? assignment 53 1

    [<Test>]
    let ``bind invocation with invalid port reference on either side is invalid`` () =
        getDiagnostic "class X : Component { dynamic x; X() { BindInstantaneous(x = ProvidedPorts.X); } }" =? reference 57 1
        getDiagnostic "class X : Component { dynamic x; X() { BindInstantaneous(RequiredPorts.X = x); } }" =? reference 75 1
        getDiagnostic "class X : Component { dynamic x; X() { BindDelayed(x = ProvidedPorts.X); } }" =? reference 51 1
        getDiagnostic "class X : Component { dynamic x; X() { BindDelayed(RequiredPorts.X = x); } }" =? reference 69 1
        getDiagnostic "class X : Component { X x; dynamic y; X() { BindInstantaneous(x.y = ProvidedPorts.X); } }" =? reference 62 3
        getDiagnostic "class X : Component { X x; dynamic y; X() { BindInstantaneous(RequiredPorts.X = x.y); } }" =? reference 80 3
        getDiagnostic "class X : Component { X x; dynamic y; X() { BindDelayed(x.y = ProvidedPorts.X); } }" =? reference 56 3
        getDiagnostic "class X : Component { X x; dynamic y; X() { BindDelayed(RequiredPorts.X = x.y); } }" =? reference 74 3

    [<Test>]
    let ``failed binding is invalid`` () =
        getDiagnostic "class X : Component { void M() {} extern void N(int i); X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); } }" =? 
            failure 80 113 ["X.N(int)"] ["X.M()"]
        getDiagnostic "class X : Component { void M() {} extern void N(int i); X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); } }" =? 
            failure 74 107 ["X.N(int)"] ["X.M()"]

    [<Test>]
    let ``ambiguous binding is invalid`` () =
        getDiagnostic "class X : Component { void M() {} void M(int i) {} extern void N(); extern void N(int i); X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); }}" =?
            ambiguous 108 141 ["X.N()"; "X.N(int)"] ["X.M()"; "X.M(int)"]
        getDiagnostic "class X : Component { void M() {} void M(int i) {} extern void N(); extern void N(int i); X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); }}" =?
            ambiguous 114 147 ["X.N()"; "X.N(int)"] ["X.M()"; "X.M(int)"]
        getDiagnostic "class X : Component { void M(int i) {} void M(ref int i) {} extern void N(int i); extern void N(ref int i); X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); }}" =?
            ambiguous 126 159 ["X.N(int)"; "X.N(ref int)"] ["X.M(int)"; "X.M(ref int)"]
        getDiagnostic "class X : Component { void M(int i) {} void M(ref int i) {} extern void N(int i); extern void N(ref int i); X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); }}" =?
            ambiguous 132 165 ["X.N(int)"; "X.N(ref int)"] ["X.M(int)"; "X.M(ref int)"]
        getDiagnostic "class X : Component { void M(int i) {} void M(ref int i) {} void M(out bool b) { b = false; } extern void N(int i); extern void N(ref int i); X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); }}" =?
            ambiguous 160 193 ["X.N(int)"; "X.N(ref int)"] ["X.M(int)"; "X.M(ref int)"]
        getDiagnostic "class X : Component { void M(int i) {} void M(ref int i) {} void M(out bool b) { b = false; } extern void N(out bool b); extern void N(int i); extern void N(ref int i); X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); }}" =?
            ambiguous 187 220 ["X.N(out bool)"; "X.N(int)"; "X.N(ref int)"] ["X.M(out bool)"; "X.M(int)"; "X.M(ref int)"]

    [<Test>]
    let ``binding is invalid when valid candidates are inaccessible`` () =
        getDiagnostic "class Y : Component { extern void N(); public extern void N(int i); } class X : Component { void M() {} X(Y y) { BindInstantaneous(y.RequiredPorts.N = ProvidedPorts.M); } }" =? 
            failure 131 166 ["Y.N(int)"] ["X.M()"]
        getDiagnostic "class Y : Component { extern void N(); public extern void N(int i); } class X : Component { void M() {} X(Y y) { BindDelayed(y.RequiredPorts.N = ProvidedPorts.M); } }" =? 
            failure 125 160 ["Y.N(int)"] ["X.M()"]

    [<Test>]
    let ``binding is unambiguous if ambiguous candidates are inaccessible`` () =
        getDiagnostic "class Y : Component { extern void N(); public extern void N(int i); } class X : Component { void M() {} void M(int i) {} X(Y y) { BindInstantaneous(y.RequiredPorts.N = ProvidedPorts.M); } }" =? None

    [<Test>]
    let ``can resolve ambiguity by explicit cast to delegate type`` () =
        getDiagnostic "class Y : Component { protected extern void N(); public extern void N(int i); } class X : Y { void M() {} void M(int i) {} X() { BindInstantaneous(RequiredPorts.N = (Action)ProvidedPorts.M); } }" =? None
        getDiagnostic "class Y : Component { protected extern void N(); public extern void N(int i); } class X : Y { void M() {} void M(int i) {} X() { BindInstantaneous(RequiredPorts.N = (Action<int>)ProvidedPorts.M); } }" =? None
        getDiagnostic "delegate void D(ref int i); class Y : Component { protected extern void N(); public extern void N(ref int i); } class X : Y { void M() {} void M(ref int i) {} X() { BindInstantaneous(RequiredPorts.N = (D)ProvidedPorts.M); } }" =? None

    [<Test>]
    let ``cast to non-delegate type is invalid`` () =
        getDiagnostic "class X : Component { void M() {} extern void N(); X() { BindDelayed(RequiredPorts.N = (int)ProvidedPorts.M); } }" =? cast 88 3
        getDiagnostic "class X : Component { void M() {} extern void N(); X() { BindDelayed(RequiredPorts.N = (object)ProvidedPorts.M); } }" =? cast 88 6
        getDiagnostic "class X : Component { void M() {} extern void N(); X() { BindDelayed(RequiredPorts.N = (Component)ProvidedPorts.M); } }" =? cast 88 9

    [<Test>]
    let ``cast to delegate type with no compatible ports is invalid`` () =
        getDiagnostic "class X : Component { void M() {} extern void N(); X() { BindDelayed(RequiredPorts.N = (Action<int>)ProvidedPorts.M); } }" =? 
            failure 69 115 ["X.N()"] []

    [<Test>]
    let ``unambiguous binding between ports of same name is valid`` () =
        getDiagnostic "class Y : Component { public extern void M(); } class X : Component { void M() {} X(Y y) { BindDelayed(y.RequiredPorts.M = ProvidedPorts.M); }}" =? None

    [<Test>]
    let ``unambiguous binding of ports with same name and different kind is valid`` () =
        getDiagnostic "class X : Component { void M() {} extern void N(); void N(int i) {} extern void M(int i); X() { BindDelayed(RequiredPorts.M = ProvidedPorts.N); } }" =? None
        getDiagnostic "class X : Component { void M() {} extern void N(); void N(int i) {} extern void M(int i); X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); } }" =? None