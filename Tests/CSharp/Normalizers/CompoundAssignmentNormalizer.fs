// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

namespace Normalization

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Diagnostics
open SafetySharp.Modeling
open SafetySharp.CSharpCompiler.Normalization
open SafetySharp.CSharpCompiler.Roslyn.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols

[<TestFixture>]
module CompoundAssignmentNormalizer =
    let normalize = TestCompilation.GetNormalizedClass (CompoundAssignmentNormalizer ())

    [<Test>]
    let ``does not normalize compound assignment outside a component class`` () =
        normalize "class X { void M() { int x = 0; x += 1; }}" =? "class X { void M() { int x = 0; x += 1; }}"

    [<Test>]
    let ``does not change simple assignment within component`` () =
        normalize "class X : Component { void M() { int x = 0; x = 1; }}" =? "class X : Component { void M() { int x = 0; x = 1; }}"

    [<Test>]
    let ``normalizes compound assignments with simple right hand side`` () =
        let check assignmentOperator expressionOperator =
            normalize (sprintf "class X : Component { void M() { int x = 0; x %s= 1; }}" assignmentOperator) =? 
                (sprintf "class X : Component { void M() { int x = 0; x = x %s (1); }}" expressionOperator)

        check "+" "+"
        check "-" "-"
        check "*" "*"
        check "/" "/"
        check "%" "%"
        check "&" "&&"
        check "|" "||"
        check "^" "^"
        check "<<" "<<"
        check ">>" ">>"

    [<Test>]
    let ``normalizes compound assignments with complex right hand side`` () =
        let check assignmentOperator expressionOperator =
            normalize (sprintf "class X : Component { void M() { int x = 0; x %s= 1 + x++ / (x - 1 * 2); }}" assignmentOperator) =? 
                (sprintf "class X : Component { void M() { int x = 0; x = x %s (1 + x++ / (x - 1 * 2)); }}" expressionOperator)

        check "+" "+"
        check "-" "-"
        check "*" "*"
        check "/" "/"
        check "%" "%"
        check "&" "&&"
        check "|" "||"
        check "^" "^"
        check "<<" "<<"
        check ">>" ">>"

    [<Test>]
    let ``normalizes nested compound assignments`` () =
        normalize "class X : Component { void M() { int x = 0, y = 0; x += y += 1; }}" =?
            "class X : Component { void M() { int x = 0, y = 0; x = x + (y = y + (1)); }}"