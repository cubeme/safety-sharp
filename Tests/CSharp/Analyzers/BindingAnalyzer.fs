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
module ``Binding ambiguity`` =
    let getDiagnostic = TestCompilation.GetDiagnostic (BindingAnalyzer ())

    let diagnostic portKind location length leftPorts rightPorts =
        createDiagnostic DiagnosticIdentifier.AmbiguousBinding (1, location) (1, location + length)
            "Port binding is ambiguous: There are multiple accessible and signature-compatible ports with the given \
			names that could be bound.\nOn the left-hand side, could be:\n%s\nOn the right-hand side, could be:\n%s" leftPorts rightPorts

    [<Test>]
    let x () =
        ()

[<TestFixture>]
module ``Binding failure`` =
    let getDiagnostic = TestCompilation.GetDiagnostic (BindingAnalyzer ())

    let diagnostic portKind location length leftPorts rightPorts =
        createDiagnostic DiagnosticIdentifier.BindingFailure (1, location) (1, location + length)
            "Port binding failure: There are no accessible signature-compatible ports with the given names that could be bound. \
		    \nOn the left-hand side, could be:\n%s\nOn the right-hand side, could be:\n%s" leftPorts rightPorts

    [<Test>]
    let x () =
        ()