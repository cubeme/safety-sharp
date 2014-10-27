// The MIT License (MIT)
// open SafetySharp.Modeling
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

namespace Roslyn.Syntax.InvocationExpressionExtensions

open System
open System.Linq
open System.Runtime.CompilerServices
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Tests
open SafetySharp.Modeling.CompilerServices
open SafetySharp.CSharpCompiler.Roslyn.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols

[<TestFixture>]
module ``IsFormulaFunctionInvocation method`` =
    let isFormulaFunctionInvocation csharpCode =
        let compilation = TestCompilation (sprintf "class X { void M() { %s; } void N() {}}" csharpCode)
        let invocation = compilation.SyntaxRoot.Descendants<InvocationExpressionSyntax>().Single ()

        invocation.IsFormulaFunctionInvocation compilation.SemanticModel

    [<Test>]
    let ``throws when invocation expression is null`` () =
        let compilation = TestCompilation ""
        raisesArgumentNullException "invocationExpression" 
            (fun () -> (null : InvocationExpressionSyntax).IsFormulaFunctionInvocation compilation.SemanticModel |> ignore)

    [<Test>]
    let ``throws when semantic model is null`` () =
        let compilation = TestCompilation "class X { void M() { M(); }}"
        let invocation = compilation.SyntaxRoot.Descendants<InvocationExpressionSyntax>().Single ()
        raisesArgumentNullException "semanticModel" (fun () -> invocation.IsFormulaFunctionInvocation null |> ignore)

    [<Test>]
    let ``returns false for non-formula invocation`` () =
        isFormulaFunctionInvocation "N()" =? false

    [<Test>]
    let ``returns true for LTL invocation`` () =
        isFormulaFunctionInvocation "Ltl.StateExpression(true)" =? true
        isFormulaFunctionInvocation "LtlFormula l = null; Ltl.Globally(l)" =? true

    [<Test>]
    let ``returns true for LTL formula invocation`` () =
        isFormulaFunctionInvocation "LtlFormula l = null; l.Implies(l);" =? true

    [<Test>]
    let ``returns true for CTL invocation`` () =
        isFormulaFunctionInvocation "Ctl.StateExpression(true)" =? true
        isFormulaFunctionInvocation "CtlFormula c = null; Ctl.AllPaths.Next(c)" =? true
        isFormulaFunctionInvocation "CtlFormula c = null; Ctl.ExistsPath.Next(c)" =? true

    [<Test>]
    let ``returns true for CTL formula invocation`` () =
        isFormulaFunctionInvocation "CtlFormula c = null; c.Implies(c);" =? true