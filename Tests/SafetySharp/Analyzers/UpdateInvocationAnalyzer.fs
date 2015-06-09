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
open SafetySharp.Compiler.Analyzers
open SafetySharp.Compiler.Roslyn.Syntax
open SafetySharp.Compiler.Roslyn.Symbols

[<TestFixture>]
module ``Update method invocation`` =
    let getDiagnostic = TestCompilation.GetDiagnostic (UpdateInvocationAnalyzer ())

    let diagnostic location length typeName =
        errorDiagnostic DiagnosticIdentifier.InvalidUpdateCall (1, location) (1, location + length)
            "'%s.Update()' cannot be called here. The Update() method of a component can only be called by the parent component's Update() method." typeName

    [<Test>]
    let ``subcomponent Update call within Update method is valid`` () =
        getDiagnostic "class Y : Component {} class X : Component { Y y; public override void Update() { y.Update();} }" =? None

    [<Test>]
    let ``base Update call within Update method is valid`` () =
        getDiagnostic "class X : Component { public override void Update() { base.Update();} }" =? None

    [<Test>]
    let ``recursive Update call within Update method is valid`` () =
        getDiagnostic "class X : Component { public override void Update() { Update();} }" =? None

    [<Test>]
    let ``Update call within constructor is valid`` () =
        getDiagnostic "class Y : Component {} class X : Component { X(Y y) { y.Update(); Update(); } }" =? None

    [<Test>]
    let ``Update call outside of component is valid`` () =
        getDiagnostic "class Y : Component {} class X { X(Y y) { y.Update(); } void Q(Y y) { y.Update(); } }" =? None

    [<Test>]
    let ``Update call in non-Update method is invalid`` () =
        getDiagnostic "class X : Component { public override void Update() {} void Q() { Update(); } }" =? diagnostic 66 8 "X"
        getDiagnostic "class X : Component { public override void Update() {} void Q() { base.Update(); } }" =? diagnostic 66 13 "SafetySharp.Modeling.Component"
        getDiagnostic "class Y : Component { public override void Update() {} } class X : Component { void Q(Y y) { y.Update(); } }" =? diagnostic 93 10 "Y"
        getDiagnostic "class X : Component { void Q() { Update(); } }" =? diagnostic 33 8 "SafetySharp.Modeling.Component" 
        getDiagnostic "class Y : Component {} class X : Component { void Q(Y y) { y.Update(); } }" =? diagnostic 59 10 "SafetySharp.Modeling.Component"

    [<Test>]
    let ``Update call in getter is invalid`` () =
        getDiagnostic "class X : Component { public override void Update() {} int Q { get { Update(); return 1; } } }" =? diagnostic 69 8 "X" 
        getDiagnostic "class X : Component { public override void Update() {} int Q { get { base.Update(); return 1; } } }" =? diagnostic 69 13 "SafetySharp.Modeling.Component" 
        getDiagnostic "class Y : Component { public override void Update() {} } class X : Component { Y y; int Q { get { y.Update(); return 1; } } }" =? diagnostic 98 10 "Y"
        getDiagnostic "class X : Component { int Q { get { Update(); return 1; } } }" =? diagnostic 36 8 "SafetySharp.Modeling.Component" 
        getDiagnostic "class Y : Component {} class X : Component { Y y; int Q { get { y.Update(); return 1; } } }" =? diagnostic 64 10 "SafetySharp.Modeling.Component"

    [<Test>]
    let ``Update call in setter is invalid`` () =
        getDiagnostic "class X : Component { public override void Update() {} int Q { set { Update(); } } }" =? diagnostic 69 8 "X" 
        getDiagnostic "class X : Component { public override void Update() {} int Q { set { base.Update(); } } }" =? diagnostic 69 13 "SafetySharp.Modeling.Component" 
        getDiagnostic "class Y : Component { public override void Update() {} } class X : Component { Y y; int Q { set { y.Update(); } } }" =? diagnostic 98 10 "Y"
        getDiagnostic "class X : Component { int Q { set { Update(); } } }" =? diagnostic 36 8 "SafetySharp.Modeling.Component" 
        getDiagnostic "class Y : Component {} class X : Component { Y y; int Q { set { y.Update(); } } }" =? diagnostic 64 10 "SafetySharp.Modeling.Component"