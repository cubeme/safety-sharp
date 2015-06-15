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
module ``Occurrence pattern`` =
    let getDiagnostic = TestCompilation.GetDiagnostic (OccurrencePatternAnalyzer ())

    let missing fault location =
        errorDiagnostic DiagnosticIdentifier.MissingOccurrencePattern (1, location) (1, location + 1) 
            "Fault '%s' does not declare a default occurrence pattern. Mark it with an attribute derived from '%s'. \
			You can change the default occurrence pattern dynamically during model initialization time."
            fault typeof<Faults.OccurrencePatternAttribute>.FullName

    let ambiguous fault location =
        errorDiagnostic DiagnosticIdentifier.AmbiguousOccurrencePattern (1, location) (1, location + 1) 
            "Fault '%s' cannot be marked with more than one occurrence pattern." fault

    let noEffect fault location =
        warningDiagnostic DiagnosticIdentifier.OccurrencePatternHasNoEffect (1, location) (1, location + 1) 
            "Occurrence patterns have no effect on classes not derived from 'SafetySharp.Modeling.Faults.Fault'."

    [<Test>]
    let ``non-fault class without an occurrence pattern is valid`` () =
        getDiagnostic "class X {}" =? None
        getDiagnostic "class X : Component {}" =? None
        getDiagnostic "namespace Y { class C : Component { class X {} }}" =? None
        getDiagnostic "namespace Y { class C : Component { class X : Component {} }}" =? None

    [<Test>]
    let ``non-fault class with one or more occurrence patterns is invalid`` () =
        getDiagnostic "[Persistent] class X {}" =? noEffect "X" 19
        getDiagnostic "[Persistent, Transient] class X : Component {}" =? noEffect "X" 30
        getDiagnostic "namespace Y { class C : Component { [Transient] class X {} }}" =? noEffect "Y.C.X" 54
        getDiagnostic "namespace Y { class C : Component { [Transient] [Persistent] class X : Component {} }}" =? noEffect "Y.C.X" 67

    [<Test>]
    let ``fault without an occurrence pattern is invalid`` () =
        getDiagnostic "class X : Fault {}" =? missing "X" 6
        getDiagnostic "namespace Y { class C : Component { class X : Fault {} }}" =? missing "Y.C.X" 42

    [<Test>]
    let ``fault with a single occurrence pattern is valid`` () =
        getDiagnostic "[Transient] class X : Fault {}" =? None
        getDiagnostic "namespace Y { class C : Component { [Persistent] class X : Fault {} }}" =? None

    [<Test>]
    let ``fault with multiple occurrence patterns is invalid`` () =
        getDiagnostic "[Transient, Persistent] class X : Fault {}" =? ambiguous "X" 30
        getDiagnostic "[Transient] [Persistent] class X : Fault {}" =? ambiguous "X" 31
        getDiagnostic "namespace Y { class C : Component { [Transient, Persistent] class X : Fault {} }}" =? ambiguous "Y.C.X" 66
        getDiagnostic "namespace Y { class C : Component { [Transient] [Persistent] class X : Fault {} }}" =? ambiguous "Y.C.X" 67