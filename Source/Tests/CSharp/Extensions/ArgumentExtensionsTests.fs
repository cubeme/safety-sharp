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

namespace SafetySharp.Tests.CSharp.Extensions.ArgumentExtensionsTests

open System
open System.Linq
open NUnit.Framework
open Swensen.Unquote
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp
open SafetySharp.Tests
open SafetySharp.Modeling
open SafetySharp.CSharp.Extensions

[<AutoOpen>]
module ArgumentExtentionsTestHelper =
    let private compilation = TestCompilation ("
        class X
        {
            public void M(int a, [LiftExpression] int b, int c)
            {
            }

            public void N(int a, [LiftExpression] params int[] b)
            {
            }

            public X()
            {
                M(1, 2, 3 + 4);
                N(1, 2, 3, 4);
                M(c: 5, a: 1, b: 3);
            }
    }")

    let methodM = compilation.FindMethodSymbol "X" "M"
    let methodN = compilation.FindMethodSymbol "X" "N"

    let invocations = compilation.SyntaxRoot.Descendants<InvocationExpressionSyntax>().ToArray();
    let semanticModel = compilation.SemanticModel;

[<TestFixture>]
module ``ParameterHasAttribute method`` =
    let parameterHasAttribute<'T when 'T :> Attribute> invocationIndex argumentIndex =
        invocations.[invocationIndex].ArgumentList.Arguments.[argumentIndex].ParameterHasAttribute<'T> semanticModel

    [<Test>]
    let ``throws when semantic model is null`` () =
        raisesArgumentNullException "semanticModel" <@ invocations.[0].ArgumentList.Arguments.[0].ParameterHasAttribute<LiftExpressionAttribute> null @>

    [<Test>]
    let ``returns false when no attribute is applied`` () =
        parameterHasAttribute<LiftExpressionAttribute> 0 0 =? false
        parameterHasAttribute<LiftExpressionAttribute> 0 2 =? false
                                                         
        parameterHasAttribute<LiftExpressionAttribute> 1 0 =? false
                                                         
        parameterHasAttribute<LiftExpressionAttribute> 2 0 =? false
        parameterHasAttribute<LiftExpressionAttribute> 2 1 =? false

    [<Test>]
    let ``returns false when different attribute is applied`` () =
        parameterHasAttribute<SealedAttribute> 0  0 =? false
        parameterHasAttribute<SealedAttribute> 0  2 =? false
       
        parameterHasAttribute<SealedAttribute> 1  0 =? false
        
        parameterHasAttribute<SealedAttribute> 2  0 =? false
        parameterHasAttribute<SealedAttribute> 2  2 =? false

    [<Test>]
    let ``returns true when the attribute is indeed applied`` () =
        parameterHasAttribute<LiftExpressionAttribute> 0  1 =? true
                                                          
        parameterHasAttribute<LiftExpressionAttribute> 1  1 =? true
        parameterHasAttribute<LiftExpressionAttribute> 1  2 =? true
        parameterHasAttribute<LiftExpressionAttribute> 1  3 =? true
                                                         
        parameterHasAttribute<LiftExpressionAttribute> 2  2 =? true

[<TestFixture>]
module ``GetMethodSymbol method`` =
    let checkMethodSymbol invocationIndex argumentIndex =
        invocations.[invocationIndex].ArgumentList.Arguments.[argumentIndex].GetMethodSymbol(semanticModel)

    [<Test>]
    let ``throws when semantic model is null`` () =
        raisesArgumentNullException "semanticModel" <@ invocations.[0].ArgumentList.Arguments.[0].GetMethodSymbol null @>

    [<Test>]
    let ``returns correct method symbol`` () =
        checkMethodSymbol 0  0 =? methodM
        checkMethodSymbol 0  1 =? methodM
        checkMethodSymbol 0  2 =? methodM
                               
        checkMethodSymbol 1  0 =? methodN
        checkMethodSymbol 1  1 =? methodN
        checkMethodSymbol 1  2 =? methodN
        checkMethodSymbol 1  3 =? methodN
                               
        checkMethodSymbol 2  0 =? methodM
        checkMethodSymbol 2  1 =? methodM
        checkMethodSymbol 2  2 =? methodM