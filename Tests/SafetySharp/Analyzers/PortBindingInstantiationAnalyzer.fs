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
open SafetySharp.Compiler.Analyzers
open SafetySharp.Compiler.Roslyn.Syntax
open SafetySharp.Compiler.Roslyn.Symbols
open SafetySharp.Runtime.Modeling

[<TestFixture>]
module ``PortBinding instantiations`` =
    let getDiagnostic = TestCompilation.GetDiagnostic (PortBindingInstantiationAnalyzer ())

    let diagnostic locationStart locationEnd =
        errorDiagnostic DiagnosticIdentifier.ExplicitPortBindingInstantiation (1, locationStart) (1, locationEnd)
            "Cannot instantiate an object of type '%s' using regular constructor syntax. Use a binding expression of \
            the form 'RequiredPorts.X = ProvidedPorts.Y' instead." typeof<PortBinding>.FullName

    [<Test>]
    let ``object instantiations are valid for other types`` () =
        getDiagnostic "class X : Component { X() { new object(); }}" =? None
        getDiagnostic "class X : Component { X() { new System.Text.StringBuilder(); }}" =? None

    [<Test>]
    let ``instantiations of port bindings are invalid`` () =
        getDiagnostic "class X : Component { X() { new PortBinding(null, null); }}" =? diagnostic 28 55