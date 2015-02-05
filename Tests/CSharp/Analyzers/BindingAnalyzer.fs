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
module ``Bindings`` =
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
        else String.Join (", ", ports |> Seq.map (sprintf "'%s'"))

    let ambiguous locationStart locationEnd leftPorts rightPorts =
        errorDiagnostic DiagnosticIdentifier.AmbiguousBinding (1, locationStart) (1, locationEnd)
            "Port binding is ambiguous: There are multiple accessible and signature-compatible ports \
			that could be bound. You can disambiguate the binding by explicitly casting one of the ports to a \
			delegate type with the signature of the port you intend to use. For instance, use 'RequiredPorts.X = \
			(Action<int>)ProvidedPorts.Y' if the port you want to bind is signature-compatible to the 'System.Action<int>' \
			delegate. Candidate ports for the left-hand side: %s. Candidate ports for the right-hand side: %s." (portList leftPorts) (portList rightPorts)

    let failure locationStart locationEnd leftPorts rightPorts =
        errorDiagnostic DiagnosticIdentifier.BindingFailure (1, locationStart) (1, locationEnd)
            "There are no accessible signature-compatible ports that could be bound. \
		     Candidate ports for the left-hand side: %s. Candidate ports for the right-hand side: %s." (portList leftPorts) (portList rightPorts)

    [<Test>]
    let ``non-failing unambiguous binding with single candidate is valid`` () =
        getDiagnostic "class X : Component { void M() {} extern void N(); X() { Bind(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M() {} extern void N(); X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); } }" =? None

    [<Test>]
    let ``non-failing unambiguous model binding with single candidate is valid`` () =
        getDiagnostic "class X : Component { public void M() {} public extern void N(); } class M : Model { X x; M() { Bind(x.RequiredPorts.N = x.ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { public void M() {} public extern void N(); } class M : Model { X x; M() { Bind(x.RequiredPorts.N = x.ProvidedPorts.M).Delayed(); } }" =? None

    [<Test>]
    let ``non-failing unambiguous binding with multiple candidates is valid`` () =
        getDiagnostic "class X : Component { void M() {} extern void N(); extern void N(int i); X() { Bind(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M() {} void M(int i) {} extern void N(); X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); } }" =? None
        getDiagnostic "class X : Component { void M(int i) {} extern void N(); extern void N(int i); X() { Bind(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M() {} void M(int i) {} extern void N(int i); X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); } }" =? None
        getDiagnostic "class X : Component { void M() {} void M(bool b) {} extern void N(); extern void N(int i); X() { Bind(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M() {} void M(int i) {} extern void N(); extern void N(bool b); X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); } }" =? None
        getDiagnostic "class X : Component { void M() {} void M(ref bool b) {} extern void N(ref bool b); extern void N(int i); X() { Bind(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M(ref int i) {} void M(int i) {} extern void N(); extern void N(ref int i); X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); } }" =? None

    [<Test>]
    let ``binding where either side yields no ports is valid`` () =
        getDiagnostic "class X : Component { extern void N(); X() { Bind(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { extern void N(); X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); } }" =? None
        getDiagnostic "class X : Component { void M() {} X() { Bind(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { void M() {} X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); } }" =? None
        getDiagnostic "class X : Component { X() { Bind(RequiredPorts.N = ProvidedPorts.M); } }" =? None
        getDiagnostic "class X : Component { X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); } }" =? None

    [<Test>]
    let ``bind invocation without port assignment is invalid`` () =
        getDiagnostic "class X : Component { X() { Bind(null); } }" =? assignment 33 4
        getDiagnostic "class X : Component { X(PortBinding p) { Bind(p); } }" =? assignment 46 1
        getDiagnostic "class X : Component { X() { Bind(null).Delayed(); } }" =? assignment 33 4
        getDiagnostic "class X : Component { X(PortBinding p) { Bind(p).Delayed(); } }" =? assignment 46 1

    [<Test>]
    let ``model bind invocation without port assignment is invalid`` () =
        getDiagnostic "class M : Model { M() { Bind(null); } }" =? assignment 29 4
        getDiagnostic "class M : Model { M(PortBinding p) { Bind(p); } }" =? assignment 42 1

    [<Test>]
    let ``bind invocation with invalid port reference on either side is invalid`` () =
        getDiagnostic "class X : Component { dynamic x; X() { Bind(x = ProvidedPorts.X); } }" =? reference 44 1
        getDiagnostic "class X : Component { dynamic x; X() { Bind(RequiredPorts.X = x); } }" =? reference 62 1
        getDiagnostic "class X : Component { dynamic x; X() { Bind(x = ProvidedPorts.X).Delayed(); } }" =? reference 44 1
        getDiagnostic "class X : Component { dynamic x; X() { Bind(RequiredPorts.X = x).Delayed(); } }" =? reference 62 1
        getDiagnostic "class X : Component { X x; dynamic y; X() { Bind(x.y = ProvidedPorts.X); } }" =? reference 49 3
        getDiagnostic "class X : Component { X x; dynamic y; X() { Bind(RequiredPorts.X = x.y); } }" =? reference 67 3
        getDiagnostic "class X : Component { X x; dynamic y; X() { Bind(x.y = ProvidedPorts.X).Delayed(); } }" =? reference 49 3
        getDiagnostic "class X : Component { X x; dynamic y; X() { Bind(RequiredPorts.X = x.y).Delayed(); } }" =? reference 67 3

    [<Test>]
    let ``model bind invocation with invalid port reference on either side is invalid`` () =
        getDiagnostic "class X : Model { dynamic x; X() { Bind(x = x.ProvidedPorts.X); } }" =? reference 40 1
        getDiagnostic "class X : Model { IComponent x; dynamic y; X() { Bind(x.RequiredPorts.y = y.ProvidedPorts.X); } }" =? reference 74 17

    [<Test>]
    let ``failed binding is invalid`` () =
        getDiagnostic "class X : Component { void M() {} extern void N(int i); X() { Bind(RequiredPorts.N = ProvidedPorts.M); } }" =? 
            failure 67 100 ["X.N(int)"] ["X.M()"]
        getDiagnostic "class X : Component { void M() {} extern void N(int i); X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); } }" =? 
            failure 67 100 ["X.N(int)"] ["X.M()"]

    [<Test>]
    let ``failed model binding is invalid`` () =
        getDiagnostic "class X : Component { public void M() {} public extern void N(int i); } class M : Model { X x; M() { Bind(x.RequiredPorts.N = x.ProvidedPorts.M); } }" =? 
            failure 106 143 ["X.N(int)"] ["X.M()"]
        getDiagnostic "class X : Component { public void M() {} public extern void N(int i); } class M : Model { X x; M() { Bind(x.RequiredPorts.N = x.ProvidedPorts.M).Delayed(); } }" =? 
            failure 106 143 ["X.N(int)"] ["X.M()"]

    [<Test>]
    let ``ambiguous binding is invalid`` () =
        getDiagnostic "class X : Component { void M() {} void M(int i) {} extern void N(); extern void N(int i); X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); }}" =?
            ambiguous 101 134 ["X.N()"; "X.N(int)"] ["X.M()"; "X.M(int)"]
        getDiagnostic "class X : Component { void M() {} void M(int i) {} extern void N(); extern void N(int i); X() { Bind(RequiredPorts.N = ProvidedPorts.M); }}" =?
            ambiguous 101 134 ["X.N()"; "X.N(int)"] ["X.M()"; "X.M(int)"]
        getDiagnostic "class X : Component { void M(int i) {} void M(ref int i) {} extern void N(int i); extern void N(ref int i); X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); }}" =?
            ambiguous 119 152 ["X.N(int)"; "X.N(ref int)"] ["X.M(int)"; "X.M(ref int)"]
        getDiagnostic "class X : Component { void M(int i) {} void M(ref int i) {} extern void N(int i); extern void N(ref int i); X() { Bind(RequiredPorts.N = ProvidedPorts.M); }}" =?
            ambiguous 119 152 ["X.N(int)"; "X.N(ref int)"] ["X.M(int)"; "X.M(ref int)"]
        getDiagnostic "class X : Component { void M(int i) {} void M(ref int i) {} void M(out bool b) { b = false; } extern void N(int i); extern void N(ref int i); X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); }}" =?
            ambiguous 153 186 ["X.N(int)"; "X.N(ref int)"] ["X.M(int)"; "X.M(ref int)"]
        getDiagnostic "class X : Component { void M(int i) {} void M(ref int i) {} void M(out bool b) { b = false; } extern void N(out bool b); extern void N(int i); extern void N(ref int i); X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); }}" =?
            ambiguous 180 213 ["X.N(out bool)"; "X.N(int)"; "X.N(ref int)"] ["X.M(out bool)"; "X.M(int)"; "X.M(ref int)"]

    [<Test>]
    let ``ambiguous model binding is invalid`` () =
        getDiagnostic "class X : Component { public void M() {} public void M(int i) {} public extern void N(); public extern void N(int i); } class M : Model { X x; M() { Bind(x.RequiredPorts.N = x.ProvidedPorts.M).Delayed(); }}" =?
            ambiguous 154 191 ["X.N()"; "X.N(int)"] ["X.M()"; "X.M(int)"]
        getDiagnostic "class X : Component { public void M() {} public void M(int i) {} public extern void N(); public extern void N(int i); } class M : Model { X x; M() { Bind(x.RequiredPorts.N = x.ProvidedPorts.M); }}" =?
            ambiguous 154 191 ["X.N()"; "X.N(int)"] ["X.M()"; "X.M(int)"]

    [<Test>]
    let ``binding is invalid when valid candidates are inaccessible`` () =
        getDiagnostic "class Y : Component { extern void N(); public extern void N(int i); } class X : Component { void M() {} X(Y y) { Bind(y.RequiredPorts.N = ProvidedPorts.M); } }" =? 
            failure 118 153 ["Y.N(int)"] ["X.M()"]
        getDiagnostic "class Y : Component { extern void N(); public extern void N(int i); } class X : Component { void M() {} X(Y y) { Bind(y.RequiredPorts.N = ProvidedPorts.M).Delayed(); } }" =? 
            failure 118 153 ["Y.N(int)"] ["X.M()"]

    [<Test>]
    let ``binding is unambiguous if ambiguous candidates are inaccessible`` () =
        getDiagnostic "class Y : Component { extern void N(); public extern void N(int i); } class X : Component { void M() {} void M(int i) {} X(Y y) { Bind(y.RequiredPorts.N = ProvidedPorts.M); } }" =? None

    [<Test>]
    let ``can resolve ambiguity by explicit cast to delegate type`` () =
        getDiagnostic "class Y : Component { protected extern void N(); public extern void N(int i); } class X : Y { void M() {} void M(int i) {} X() { Bind(RequiredPorts.N = (Action)ProvidedPorts.M); } }" =? None
        getDiagnostic "class Y : Component { protected extern void N(); public extern void N(int i); } class X : Y { void M() {} void M(int i) {} X() { Bind(RequiredPorts.N = (Action<int>)ProvidedPorts.M); } }" =? None
        getDiagnostic "delegate void D(ref int i); class Y : Component { protected extern void N(); public extern void N(ref int i); } class X : Y { void M() {} void M(ref int i) {} X() { Bind(RequiredPorts.N = (D)ProvidedPorts.M); } }" =? None

    [<Test>]
    let ``cast to non-delegate type is invalid`` () =
        getDiagnostic "class X : Component { void M() {} extern void N(); X() { Bind(RequiredPorts.N = (int)ProvidedPorts.M).Delayed(); } }" =? cast 81 3
        getDiagnostic "class X : Component { void M() {} extern void N(); X() { Bind(RequiredPorts.N = (object)ProvidedPorts.M).Delayed(); } }" =? cast 81 6
        getDiagnostic "class X : Component { void M() {} extern void N(); X() { Bind(RequiredPorts.N = (Component)((ProvidedPorts.M))).Delayed(); } }" =? cast 81 9

    [<Test>]
    let ``cast to delegate type with no compatible ports is invalid`` () =
        getDiagnostic "class X : Component { void M() {} extern void N(); X() { Bind(RequiredPorts.N = (Action<int>)ProvidedPorts.M).Delayed(); } }" =? 
            failure 62 108 ["X.N()"] []

    [<Test>]
    let ``unambiguous binding between ports of same name is valid`` () =
        getDiagnostic "class Y : Component { public extern void M(); } class X : Component { void M() {} X(Y y) { Bind(y.RequiredPorts.M = ProvidedPorts.M).Delayed(); }}" =? None

    [<Test>]
    let ``binding with many parentheses is valid`` () =
        getDiagnostic "class Y : Component { public extern void M(); } class X : Component { void M() {} X(Y y) { Bind(((((y).RequiredPorts).M) = (ProvidedPorts.M))).Delayed(); }}" =? None

    [<Test>]
    let ``unambiguous binding of ports with same name and different kind is valid`` () =
        getDiagnostic "class X : Component { void M() {} extern void N(); void N(int i) {} extern void M(int i); X() { Bind(RequiredPorts.M = ProvidedPorts.N).Delayed(); } }" =? None
        getDiagnostic "class X : Component { void M() {} extern void N(); void N(int i) {} extern void M(int i); X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); } }" =? None

    [<Test>]
    let ``model binding is unambiguous if ambiguous candidates are inaccessible`` () =
        getDiagnostic "class Y : Component { extern void N(); public extern void N(int i); } class X : Component { void M() {} public void M(int i) {} } class M : Model { X x; Y y; M() { Bind(y.RequiredPorts.N = x.ProvidedPorts.M); } }" =? None

    [<Test>]
    let ``model bindingcan resolve ambiguity by explicit cast to delegate type`` () =
        getDiagnostic "class Y : Component { public extern void N(); public extern void N(int i); } class X : Y { public void M() {} public void M(int i) {} } class M : Model { X x; M() { Bind(x.RequiredPorts.N = (Action)x.ProvidedPorts.M); } }" =? None
        getDiagnostic "class Y : Component { public extern void N(); public extern void N(int i); } class X : Y { public void M() {} public void M(int i) {} } class M : Model { X x; M() { Bind(x.RequiredPorts.N = (Action<int>)x.ProvidedPorts.M); } }" =? None
        getDiagnostic "delegate void D(ref int i); class Y : Component { public extern void N(); public extern void N(ref int i); } class X : Y { public void M() {} public void M(ref int i) {} } class M : Model { X x; M() { Bind(x.RequiredPorts.N = (D)x.ProvidedPorts.M); } }" =? None

    [<Test>]
    let ``model binding cast to non-delegate type is invalid`` () =
        getDiagnostic "class X : Component { public void M() {} public extern void N(); } class M : Model { X x; M() { Bind(x.RequiredPorts.N = (int)x.ProvidedPorts.M).Delayed(); } }" =? cast 122 3
        getDiagnostic "class X : Component { public void M() {} public extern void N(); } class M : Model { X x; M() { Bind(x.RequiredPorts.N = (object)x.ProvidedPorts.M).Delayed(); } }" =? cast 122 6
        getDiagnostic "class X : Component { public void M() {} public extern void N(); } class M : Model { X x; M() { Bind(x.RequiredPorts.N = (Component)((x.ProvidedPorts.M))).Delayed(); } }" =? cast 122 9
    
    [<Test>]
    let ``binding of Update method is valid`` () = 
        getDiagnostic "class X : Component { void M() {} X() { Bind(RequiredPorts.Update = ProvidedPorts.M); } public override void Update() {}}" =? None
        getDiagnostic "class X : Component { extern void M(); X() { Bind(RequiredPorts.M = ProvidedPorts.Update); } public override void Update() {}}" =? None

    [<Test>]
    let ``overridden provided ports are only considered once`` () =
        getDiagnostic "class X : Component { public virtual void M() {}} class Y : X { extern void N(); public override void M() {} Y() { Bind(RequiredPorts.N = ProvidedPorts.M); }}" =? None

    [<Test>]
    let ``overridden required ports are only considered once`` () =
        getDiagnostic "class X : Component { public virtual extern void M(); } class Y : X { void N() {} public extern override void M(); Y() { Bind(RequiredPorts.M = ProvidedPorts.N); }}" =? None

    [<Test>]
    let ``new and original provided ports are both considered causing an ambiguity`` () =
        getDiagnostic "class X : Component { public void M() {}} class Y : X { extern void N(); public new void M() {} Y() { Bind(RequiredPorts.N = ProvidedPorts.M); }}" =? 
            ambiguous 107 140 ["Y.N()"] ["Y.M()"; "X.M()"]

    [<Test>]
    let ``new and original required ports are both considered causing an ambiguity`` () =
        getDiagnostic "class X : Component { public extern void M(); } class Y : X { void N() {} public extern new void M(); Y() { Bind(RequiredPorts.M = ProvidedPorts.N); }}" =? 
            ambiguous 113 146 ["Y.M()"; "X.M()"] ["Y.N()"]

    [<Test>]
    let ``provided port replaced by new required port`` () =
        getDiagnostic "class X : Component { public void M() {}} class Y : X { void N() {} public extern new void M(); Y() { Bind(RequiredPorts.M = ProvidedPorts.N); }}" =? None

    [<Test>]
    let ``required port replaced by new provided port`` () =
        getDiagnostic "class X : Component { public extern void M(); } class Y : X { extern void N(); public new void M() {} Y() { Bind(RequiredPorts.N = ProvidedPorts.M); }}" =? None
