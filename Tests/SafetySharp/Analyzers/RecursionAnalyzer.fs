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
open SafetySharp.Compiler.Roslyn
open SafetySharp.Compiler.Roslyn.Syntax
open SafetySharp.Compiler.Roslyn.Symbols

[<TestFixture>]
module ``Recursion`` =
    let getDiagnostic = TestCompilation.GetDiagnostic (RecursionAnalyzer ())
    let getDiagnostics = TestCompilation.GetDiagnostics (RecursionAnalyzer ())

    let recursion location length =
        errorDiagnostic DiagnosticIdentifier.Recursion (1, location) (1, location + length)
            "Recursive method or property accessor invocation is not allowed here."

    let recursions locations lengths =
        List.zip locations lengths |> List.map (fun (location, length) -> recursion location length) |> List.map Option.get

    let mutualRecursion location length (cycle : string list) =
        let cycle = String.Join (", ", cycle |> Seq.map (sprintf "'%s'"))
        errorDiagnostic DiagnosticIdentifier.MutualRecursion (1, location) (1, location + length)
            "Mutually recursive method or property accessor invocations are not allowed here. The recursion involves: %s." cycle

    let mutualRecursions locations lengths cycles =
        List.zip3 locations lengths cycles |> List.map (fun (location, length, cycle) -> mutualRecursion location length cycle) |> List.map Option.get

    [<Test>]
    let ``recursive call outside of component is valid`` () =
        getDiagnostic "class X { void M() { M(); } }" =? None

    [<Test>]
    let ``recursive call outside of component in expression-bodied method is valid`` () =
        getDiagnostic "class X { void M() => M(); }" =? None

    [<Test>]
    let ``mutually recursive calls outside of component is valid`` () =
        getDiagnostic "class X { void M() { N(); } void N() { M(); } }" =? None

    [<Test>]
    let ``non-recursive method call is valid`` () =
        getDiagnostic "class X : Component { void M() { N(); } void N() {} }" =? None

    [<Test>]
    let ``non-recursive method call in expression-bodied method is valid`` () =
        getDiagnostic "class X : Component { void M() => N(); void N() {} }" =? None

    [<Test>]
    let ``non-recursive getter call is valid`` () =
        getDiagnostic "class X : Component { int N { get; set; } int M { get { return N; } } }" =? None
        getDiagnostic "class X : Component { int M { get { return 1; } set { var m = M; } } }" =? None

    [<Test>]
    let ``non-recursive setter call is valid`` () =
        getDiagnostic "class X : Component { int N { get; set; } int M { set { N = value; } } }" =? None
        getDiagnostic "class X : Component { int M { get { return M = 3; } set {} } }" =? None

    [<Test>]
    let ``recursive method call is invalid`` () =
        getDiagnostic "class X : Component { void M() { M(); } }" =? recursion 33 3
        getDiagnostic "class X : Component { int N(int i) { return i; } int M() { return N(M()); } }" =? recursion 68 3

    [<Test>]
    let ``multiple recursive method calls are invalid`` () =
        getDiagnostics "class X : Component { int N(int i) { return i; } int M() { return M() + N(M()); } }" =? recursions [66; 74] [3; 3]

    [<Test>]
    let ``recursive getter call is invalid`` () =
        getDiagnostic "class X : Component { int M { get { var m = M; return m; } } }" =? recursion 44 1
        getDiagnostic "class X : Component { int N(int i) { return i; } int M { get { return N(M); } } }" =? recursion 72 1

    [<Test>]
    let ``recursive expression-bodied getter call is invalid`` () =
        getDiagnostic "class X : Component { int M => M; }" =? recursion 31 1

    [<Test>]
    let ``multiple recursive getter calls are invalid`` () =
        getDiagnostics "class X : Component { bool M { get { var m = M == M; return m; } } }" =? recursions [45; 50] [1; 1]

    [<Test>]
    let ``recursive setter call is invalid`` () =
        getDiagnostic "class X : Component { int M { set { M = value; } } }" =? recursion 36 1
        getDiagnostic "class X : Component { int M { set { var i = M = value; } } }" =? recursion 44 1

    [<Test>]
    let ``multiple recursive setter calls are invalid`` () =
        getDiagnostics "class X : Component { int M { set { M = M = value; } } }" =? recursions [36; 40] [1; 1]

    [<Test>]
    let ``mutual method recursion is invalid`` () =
        getDiagnostic "class X : Component { void A() { B(); } void B() { A(); } }" =? mutualRecursion 27 1 ["X.A()"; "X.B()"]
        getDiagnostic "class X : Component { void A() { B(); } void B() { C(); } void C() { D(); } void D() { A(); } }" =? mutualRecursion 27 1 ["X.A()"; "X.B()"; "X.C()"; "X.D()"]

    [<Test>]
    let ``mutual getter recursion is invalid`` () =
        getDiagnostic "class X : Component { int A { get { return B; } } int B { get { return A; } } }" =? mutualRecursion 30 3 ["X.A.get"; "X.B.get"]
        getDiagnostic "class X : Component { int A { get { return B; } } int B { get { return C; } } int C { get { return D; } } int D { get { return A; } } }" =? mutualRecursion 30 3 ["X.A.get"; "X.B.get"; "X.C.get"; "X.D.get"]

    [<Test>]
    let ``mutual setter recursion is invalid`` () =
        getDiagnostic "class X : Component { int A { set { B = value; } } int B { set { A = value; } } }" =? mutualRecursion 30 3 ["X.A.set"; "X.B.set"]
        getDiagnostic "class X : Component { int A { set { B = value; } } int B { set { C = value; } } int C { set { D = value; } } int D { set { A = value; } } }" =? mutualRecursion 30 3 ["X.A.set"; "X.B.set"; "X.C.set"; "X.D.set"]

    [<Test>]
    let ``chain of recursive method and accessor invocations`` () =
        getDiagnostic "class X : Component { \
                            int A { get { return B(); } } \
                            int B() { return C = 3; } \
                            int C { set { D(value); } } \
                            void D(int i) { i += A; }
                       }" =? mutualRecursion 56 1 ["X.B()"; "X.C.set"; "X.D(int)"; "X.A.get"]

    [<Test>]
    let ``multiple mutual method recursions are invalid`` () =
        getDiagnostics "class X : Component { void A() { B(); } void B() { A(); } void C() { D(); } void D() { C(); } }" =?
            mutualRecursions [27; 63] [1; 1] [["X.A()"; "X.B()"]; ["X.C()"; "X.D()"]]

    [<Test>]
    let ``multiple mutual getter recursions are invalid`` () =
        getDiagnostics "class X : Component { int A { get { return B; } } int B { get { return A; } } int C { get { return D; } } int D { get { return C; } } }" =? 
            mutualRecursions [30; 86] [3; 3] [["X.A.get"; "X.B.get"]; ["X.C.get"; "X.D.get"]]

    [<Test>]
    let ``multiple mutual setter recursions are invalid`` () =
        getDiagnostics "class X : Component { int A { set { B = value; } } int B { set { A = value; } } int C { set { D = value; } } int D { set { C = value; } } }" =? 
            mutualRecursions [30; 88] [3; 3] [["X.A.set"; "X.B.set"]; ["X.C.set"; "X.D.set"]]
