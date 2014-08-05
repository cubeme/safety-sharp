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
open SafetySharp.Tests
open SafetySharp.Modeling
open SafetySharp.CSharpCompiler.Normalization
open SafetySharp.CSharpCompiler.Roslyn.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols

[<TestFixture>]
module ExpressionLifter =
    let normalize csharpCode =
        let compilation = TestCompilation (sprintf "
            class C : Component
            {
                C(bool b) {}
                C([LiftExpression] int i) {}

                int M(int i) { return 0; }
                int N([LiftExpression] int i) { return 0; }
                int O([LiftExpression] int i, [LiftExpression] int j) { return 0; }
                int P(int i, [LiftExpression] bool b) { return 0; }

                void Test() { %s; }
            }" csharpCode)

        let syntaxTree = ExpressionLifter().Normalize(compilation.CSharpCompilation).SyntaxTrees.Single ()
        let creationInvocation = syntaxTree.Descendants<ObjectCreationExpressionSyntax>().FirstOrDefault ()
        
        if creationInvocation <> null then
            creationInvocation.ToString ()
        else
            let methodInvocation = syntaxTree.Descendants<InvocationExpressionSyntax>().FirstOrDefault ()
            methodInvocation.ToString ()

    [<Test>]
    let ``does not lift method invocation argument that does not require lifting`` () =
        normalize "M(30)" =? "M(30)"

    [<Test>]
    let ``does not lift object creation argument that does not require lifting`` () =
        normalize "new C(false)" =? "new C(false)"

    [<Test>]
    let ``lifts object creation argument`` () =
        normalize "new C(1)" =? "new C(() => 1)"
        normalize "new C(1 + 3 / 54 + (true == false ? 17 : 33 + 1))" =? "new C(() => 1 + 3 / 54 + (true == false ? 17 : 33 + 1))"

    [<Test>]
    let ``lifts method invocation argument`` () =
        normalize "N(1)" =? "N(() => 1)"
        normalize "N(1 + 3 / 54 + (true == false ? 17 : 33 + 1))" =? "N(() => 1 + 3 / 54 + (true == false ? 17 : 33 + 1))"

    [<Test>]
    let ``lifts both method invocation arguments`` () =
        normalize "O(1, 17)" =? "O(() => 1, () => 17)"
        normalize "O(1, 1 + 3)" =? "O(() => 1, () => 1 + 3)"
        normalize "O(1 - 0, 3)" =? "O(() => 1 - 0, () => 3)"

    [<Test>]
    let ``lifts second method invocation argument`` () =
        normalize "P(1, true)" =? "P(1, () => true)"
        normalize "P(1, true || false)" =? "P(1, () => true || false)"
        normalize "P(1 - 0, false)" =? "P(1 - 0, () => false)"

    [<Test>]
    let ``lifts nested method invocations and object creations`` () =
        normalize "new C(O(M(1), N(17 + 1)))" =? "new C(() => O(() => M(1), () => N(() => 17 + 1)))"

    [<Test>]
    let ``preserves all line breaks in expressions`` () =
        normalize "new C(1\n + 1)" =? "new C(() => 1\n + 1)"
        normalize "O(M(2 -\n1)\n+ 0,\n3\n- N(\n2 *\n5))" =? "O(() => M(2 -\n1)\n+ 0,\n() => 3\n- N(\n() => 2 *\n5))"