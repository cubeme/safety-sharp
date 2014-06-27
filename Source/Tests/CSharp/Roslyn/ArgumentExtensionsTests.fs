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

namespace SafetySharp.Tests.CSharp.Roslyn.ArgumentExtensionsTests

open System
open System.Linq
open NUnit.Framework
open Swensen.Unquote
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp
open SafetySharp.Tests
open SafetySharp.Modeling
open SafetySharp.CSharp.Roslyn

[<AutoOpen>]
module ArgumentExtentionsTestHelper =
    let private compilation = TestCompilation ("
        using System;
        using System.Linq.Expressions;
        class X
        {
            public X(int a, [LiftExpression] int b)
            {
            }

            public void M(int a, [LiftExpression] int b, int c)
            {
            }

            public void N(int a, [LiftExpression] params int[] b)
            {
            }

            public void O(bool x, decimal d)
            {
            }

            public void P([LiftExpression] bool x, Expression<Func<bool>> d, Expression<Func<int>> i, bool y)
            {
            }

            public X()
            {
                M(1, 2, 3 + 4);
                N(1, 2, 3, 4);
                M(c: 5, a: 1, b: 3);
                new X(3, 6);
                new X(b: 7, a: 11);
                O(true, 3.14m);
                P(true, () => false, () => 2, false);
            }
    }")

    let methodM = compilation.FindMethodSymbol "X" "M"
    let methodN = compilation.FindMethodSymbol "X" "N"
    let constructorSymbol = compilation.FindClassSymbol("X").Constructors.[0]

    let invocations = compilation.SyntaxRoot.Descendants<InvocationExpressionSyntax>().ToArray ()
    let invokeMethodO = compilation.SyntaxRoot.Descendants<InvocationExpressionSyntax>().Skip(3).First ()
    let invokeMethodP = compilation.SyntaxRoot.Descendants<InvocationExpressionSyntax>().Last ()
    let creations = compilation.SyntaxRoot.Descendants<ObjectCreationExpressionSyntax>().ToArray ()
    let semanticModel = compilation.SemanticModel

[<TestFixture>]
module ``ParameterHasAttribute method`` =
    let parameterHasAttribute<'T when 'T :> Attribute> invocationIndex argumentIndex =
        invocations.[invocationIndex].ArgumentList.Arguments.[argumentIndex].HasAttribute<'T> semanticModel

    let constructorParameterHasAttribute<'T when 'T :> Attribute> invocationIndex argumentIndex =
        creations.[invocationIndex].ArgumentList.Arguments.[argumentIndex].HasAttribute<'T> semanticModel

    [<Test>]
    let ``throws when semantic model is null`` () =
        raisesArgumentNullException "semanticModel" <@ invocations.[0].ArgumentList.Arguments.[0].HasAttribute<LiftExpressionAttribute> null @>

    [<Test>]
    let ``returns false when no attribute is applied`` () =
        parameterHasAttribute<LiftExpressionAttribute> 0 0 =? false
        parameterHasAttribute<LiftExpressionAttribute> 0 2 =? false
                                                         
        parameterHasAttribute<LiftExpressionAttribute> 1 0 =? false
                                                         
        parameterHasAttribute<LiftExpressionAttribute> 2 0 =? false
        parameterHasAttribute<LiftExpressionAttribute> 2 1 =? false

        constructorParameterHasAttribute<LiftExpressionAttribute> 0 0 =? false
        constructorParameterHasAttribute<LiftExpressionAttribute> 1 1 =? false

    [<Test>]
    let ``returns false when different attribute is applied`` () =
        parameterHasAttribute<SealedAttribute> 0  0 =? false
        parameterHasAttribute<SealedAttribute> 0  2 =? false
       
        parameterHasAttribute<SealedAttribute> 1  0 =? false
        
        parameterHasAttribute<SealedAttribute> 2  0 =? false
        parameterHasAttribute<SealedAttribute> 2  2 =? false

        constructorParameterHasAttribute<SealedAttribute> 0 1 =? false
        constructorParameterHasAttribute<SealedAttribute> 1 0 =? false

    [<Test>]
    let ``returns true when the attribute is indeed applied`` () =
        parameterHasAttribute<LiftExpressionAttribute> 0  1 =? true
                                                          
        parameterHasAttribute<LiftExpressionAttribute> 1  1 =? true
        parameterHasAttribute<LiftExpressionAttribute> 1  2 =? true
        parameterHasAttribute<LiftExpressionAttribute> 1  3 =? true
                                                         
        parameterHasAttribute<LiftExpressionAttribute> 2  2 =? true

        constructorParameterHasAttribute<LiftExpressionAttribute> 0 1 =? true
        constructorParameterHasAttribute<LiftExpressionAttribute> 1 0 =? true

[<TestFixture>]
module ``GetMethodSymbol method`` =
    let getMethodSymbol invocationIndex argumentIndex =
        invocations.[invocationIndex].ArgumentList.Arguments.[argumentIndex].GetMethodSymbol semanticModel

    let getConstructorSymbol invocationIndex argumentIndex =
        creations.[invocationIndex].ArgumentList.Arguments.[argumentIndex].GetMethodSymbol semanticModel

    [<Test>]
    let ``throws when semantic model is null`` () =
        raisesArgumentNullException "semanticModel" <@ invocations.[0].ArgumentList.Arguments.[0].GetMethodSymbol null @>

    [<Test>]
    let ``returns correct method symbol`` () =
        getMethodSymbol 0  0 =? methodM
        getMethodSymbol 0  1 =? methodM
        getMethodSymbol 0  2 =? methodM
                               
        getMethodSymbol 1  0 =? methodN
        getMethodSymbol 1  1 =? methodN
        getMethodSymbol 1  2 =? methodN
        getMethodSymbol 1  3 =? methodN
                               
        getMethodSymbol 2  0 =? methodM
        getMethodSymbol 2  1 =? methodM
        getMethodSymbol 2  2 =? methodM

        getConstructorSymbol 0 0 =? constructorSymbol
        getConstructorSymbol 0 1 =? constructorSymbol
        getConstructorSymbol 1 0 =? constructorSymbol
        getConstructorSymbol 1 1 =? constructorSymbol

[<TestFixture>]
module ``IsOfType method`` =
    [<Test>]
    let ``throws when semantic model is null`` () =
        raisesArgumentNullException "semanticModel" <@ invokeMethodO.ArgumentList.Arguments.[0].IsOfType<bool> null @>

    [<Test>]
    let ``returns true for correct types`` () =
        invokeMethodO.ArgumentList.Arguments.[0].IsOfType<bool> semanticModel =? true
        invokeMethodO.ArgumentList.Arguments.[1].IsOfType<decimal> semanticModel =? true

        invokeMethodO.ArgumentList.Arguments.[0].IsOfType (semanticModel, semanticModel.GetTypeSymbol<bool> ()) =? true
        invokeMethodO.ArgumentList.Arguments.[1].IsOfType (semanticModel, semanticModel.GetTypeSymbol<decimal> ()) =? true

    [<Test>]
    let ``returns false for incorrect types`` () =
        invokeMethodO.ArgumentList.Arguments.[0].IsOfType<int> semanticModel =? false
        invokeMethodO.ArgumentList.Arguments.[1].IsOfType<bool> semanticModel =? false

        invokeMethodO.ArgumentList.Arguments.[0].IsOfType (semanticModel, semanticModel.GetTypeSymbol<int> ()) =? false
        invokeMethodO.ArgumentList.Arguments.[1].IsOfType (semanticModel, semanticModel.GetTypeSymbol<bool> ()) =? false

[<TestFixture>]
module ``IsBooleanExpressionArgument method`` =
    [<Test>]
    let ``throws when semantic model is null`` () =
        raisesArgumentNullException "semanticModel" <@ invokeMethodO.ArgumentList.Arguments.[0].IsBooleanExpressionArgument null @>

    [<Test>]
    let ``returns true for Boolean arguments`` () =
        invokeMethodP.ArgumentList.Arguments.[0].IsBooleanExpressionArgument semanticModel =? true

    [<Test>]
    let ``returns true for Expression<Func<bool>> arguments`` () =
        invokeMethodP.ArgumentList.Arguments.[1].IsBooleanExpressionArgument semanticModel =? true

    [<Test>]
    let ``returns false for non-Boolean arguments`` () =    
        invokeMethodO.ArgumentList.Arguments.[1].IsBooleanExpressionArgument semanticModel =? false

    [<Test>]
    let ``returns false for non-Boolean expression arguments`` () =    
        invokeMethodP.ArgumentList.Arguments.[2].IsBooleanExpressionArgument semanticModel =? false

    [<Test>]
    let ``returns false for Boolean arguments without the [LiftExpression] attribute`` () =
        invokeMethodP.ArgumentList.Arguments.[3].IsBooleanExpressionArgument semanticModel =? false