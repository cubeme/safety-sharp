// The MIT License (MIT)
// open SafetySharp.Modeling
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

namespace Roslyn.Syntax.ArgumentExtensions

open System
open System.Linq
open System.Runtime.CompilerServices
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Modeling.CompilerServices
open SafetySharp.CSharp.Roslyn.Syntax
open SafetySharp.CSharp.Roslyn.Symbols

[<AutoOpen>]
module Helpers =
    let compilation = TestCompilation ("
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
module ``HasAttribute method`` =
    let parameterHasAttribute<'T when 'T :> Attribute> invocationIndex argumentIndex =
        invocations.[invocationIndex].ArgumentList.Arguments.[argumentIndex].HasAttribute<'T> semanticModel

    let constructorParameterHasAttribute<'T when 'T :> Attribute> invocationIndex argumentIndex =
        creations.[invocationIndex].ArgumentList.Arguments.[argumentIndex].HasAttribute<'T> semanticModel

    [<Test>]
    let ``throws when argument is null`` () =
        raisesArgumentNullException "argument" (fun () -> (null : ArgumentSyntax).HasAttribute<LiftExpressionAttribute> compilation.SemanticModel |> ignore)

    [<Test>]
    let ``throws when semantic model is null`` () =
        raisesArgumentNullException "semanticModel" (fun () -> invocations.[0].ArgumentList.Arguments.[0].HasAttribute<LiftExpressionAttribute> null |> ignore)

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
        parameterHasAttribute<CompilerGeneratedAttribute> 0  0 =? false
        parameterHasAttribute<CompilerGeneratedAttribute> 0  2 =? false
       
        parameterHasAttribute<CompilerGeneratedAttribute> 1  0 =? false
        
        parameterHasAttribute<CompilerGeneratedAttribute> 2  0 =? false
        parameterHasAttribute<CompilerGeneratedAttribute> 2  2 =? false

        constructorParameterHasAttribute<CompilerGeneratedAttribute> 0 1 =? false
        constructorParameterHasAttribute<CompilerGeneratedAttribute> 1 0 =? false

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
    let ``throws when argument is null`` () =
        raisesArgumentNullException "argument" (fun () -> (null : ArgumentSyntax).GetMethodSymbol compilation.SemanticModel |> ignore)

    [<Test>]
    let ``throws when semantic model is null`` () =
        raisesArgumentNullException "semanticModel" (fun () -> invocations.[0].ArgumentList.Arguments.[0].GetMethodSymbol null |> ignore)

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
module ``IsOfType methods`` =
    [<Test>]
    let ``throws when argument is null`` () =
        let symbol = compilation.CSharpCompilation.GetTypeSymbol<bool> ()
        raisesArgumentNullException "argument" (fun () -> (null : ArgumentSyntax).IsOfType<bool> compilation.SemanticModel |> ignore)
        raisesArgumentNullException "argument" (fun () -> (null : ArgumentSyntax).IsOfType (compilation.SemanticModel, symbol) |> ignore)

    [<Test>]
    let ``throws when semantic model is null`` () =
        let symbol = compilation.CSharpCompilation.GetTypeSymbol<bool> ()
        raisesArgumentNullException "semanticModel" (fun () -> invokeMethodO.ArgumentList.Arguments.[0].IsOfType<bool> null |> ignore)
        raisesArgumentNullException "semanticModel" (fun () -> invokeMethodO.ArgumentList.Arguments.[0].IsOfType (null, symbol) |> ignore)

    [<Test>]
    let ``throws when argument type is null`` () =
        raisesArgumentNullException "argumentType" (fun () -> invokeMethodO.ArgumentList.Arguments.[0].IsOfType (compilation.SemanticModel, null) |> ignore)

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
    let ``throws when argument is null`` () =
        raisesArgumentNullException "argument" (fun () -> (null : ArgumentSyntax).IsBooleanExpression compilation.SemanticModel |> ignore)

    [<Test>]
    let ``throws when semantic model is null`` () =
        raisesArgumentNullException "semanticModel" (fun () -> invokeMethodO.ArgumentList.Arguments.[0].IsBooleanExpression null |> ignore)

    [<Test>]
    let ``returns true for Boolean arguments`` () =
        invokeMethodP.ArgumentList.Arguments.[0].IsBooleanExpression semanticModel =? true

    [<Test>]
    let ``returns true for Expression<Func<bool>> arguments`` () =
        invokeMethodP.ArgumentList.Arguments.[1].IsBooleanExpression semanticModel =? true

    [<Test>]
    let ``returns false for non-Boolean arguments`` () =    
        invokeMethodO.ArgumentList.Arguments.[1].IsBooleanExpression semanticModel =? false

    [<Test>]
    let ``returns false for non-Boolean expression arguments`` () =    
        invokeMethodP.ArgumentList.Arguments.[2].IsBooleanExpression semanticModel =? false

    [<Test>]
    let ``returns false for Boolean arguments without the [LiftExpression] attribute`` () =
        invokeMethodP.ArgumentList.Arguments.[3].IsBooleanExpression semanticModel =? false

[<TestFixture>]
module ``GetMethodCallExpression method`` =
    [<Test>]
    let ``throws when argument is null`` () =
        raisesArgumentNullException "argument" (fun () -> (null : ArgumentSyntax).GetMethodCallExpression () |> ignore)

    [<Test>]
    let ``returns correct invocation expression`` () =
        let compilation = TestCompilation "class C { void X() { N(1); } void Y() { N(O(2)); } void N(int i) {} int O(int i) { return i; }}"
        let invokeNInX = 
            let methodBody = compilation.FindMethodDeclaration "C" "X"
            methodBody.Descendants<InvocationExpressionSyntax>().Single ()
        let invokeNInY = 
            let methodBody = compilation.FindMethodDeclaration "C" "X"
            methodBody.Descendants<InvocationExpressionSyntax>().First ()
        let invokeOInY =
            let methodBody = compilation.FindMethodDeclaration "C" "Y"
            methodBody.Descendants<InvocationExpressionSyntax>().Skip(1).Single ()

        let argumentNInX = invokeNInX.Descendants<ArgumentSyntax>().Single ()
        let argumentNInY = invokeNInY.Descendants<ArgumentSyntax>().First ()
        let argumentOInY = invokeOInY.Descendants<ArgumentSyntax>().Single ()

        argumentNInX.GetMethodCallExpression () :?> InvocationExpressionSyntax =? invokeNInX
        argumentNInY.GetMethodCallExpression () :?> InvocationExpressionSyntax =? invokeNInY
        argumentOInY.GetMethodCallExpression () :?> InvocationExpressionSyntax =? invokeOInY

    [<Test>]
    let ``returns correct object creation expression`` () =
        let compilation = TestCompilation "class B { public B(int i) {} }
            class C { public C(B b) {} void X() { new B(1); } void Y() { new C(new B(1)); } void Z() { N(new B(1)); } void N(B b) {}}"

        let createBInX = 
            let methodBody = compilation.FindMethodDeclaration "C" "X"
            methodBody.Descendants<ObjectCreationExpressionSyntax>().Single ()
        let createBInY =
            let methodBody = compilation.FindMethodDeclaration "C" "Y"
            methodBody.Descendants<ObjectCreationExpressionSyntax>().Skip(1).Single ()
        let createCInY =
            let methodBody = compilation.FindMethodDeclaration "C" "Y"
            methodBody.Descendants<ObjectCreationExpressionSyntax>().First ()
        let createBInZ =
            let methodBody = compilation.FindMethodDeclaration "C" "Z"
            methodBody.Descendants<ObjectCreationExpressionSyntax>().Single ()
        let invokeNInZ =
            let methodBody = compilation.FindMethodDeclaration "C" "Z"
            methodBody.Descendants<InvocationExpressionSyntax>().Single ()

        let argumentInX = createBInX.Descendants<ArgumentSyntax>().Single ()
        let argumentBInY = createBInY.Descendants<ArgumentSyntax>().Single ()
        let argumentCInY = createCInY.Descendants<ArgumentSyntax>().First ()
        let argumentBInZ = createBInZ.Descendants<ArgumentSyntax>().Single ()
        let argumentNInZ = invokeNInZ.Descendants<ArgumentSyntax>().First ()

        argumentInX .GetMethodCallExpression () :?> ObjectCreationExpressionSyntax =? createBInX
        argumentBInY.GetMethodCallExpression () :?> ObjectCreationExpressionSyntax =? createBInY
        argumentCInY.GetMethodCallExpression () :?> ObjectCreationExpressionSyntax =? createCInY
        argumentBInZ.GetMethodCallExpression () :?> ObjectCreationExpressionSyntax =? createBInZ
        argumentNInZ.GetMethodCallExpression () :?> InvocationExpressionSyntax =? invokeNInZ

[<TestFixture>]
module ``GetParameterSymbol method`` =
    [<Test>]
    let ``throws when argument is null`` () =
        raisesArgumentNullException "argument" (fun () -> (null : ArgumentSyntax).GetParameterSymbol compilation.SemanticModel |> ignore)

    [<Test>]
    let ``throws when semantic model is null`` () =
        raisesArgumentNullException "semanticModel" (fun () -> invokeMethodO.ArgumentList.Arguments.[0].GetParameterSymbol null |> ignore)

    [<Test>]
    let ``returns correct parameter symbol`` () =
        let compilation = TestCompilation "class X { void M() { N(1, 2); } void N(int i, int j) {} }"
        let methodM = compilation.FindMethodDeclaration "X" "M"
        let methodSymbol = compilation.FindMethodSymbol "X" "N"
        let argument1 = methodM.Descendants<ArgumentSyntax>().First ()
        let argument2 = methodM.Descendants<ArgumentSyntax>().Skip(1).Single ()

        argument1.GetParameterSymbol compilation.SemanticModel =? methodSymbol.Parameters.[0]
        argument2.GetParameterSymbol compilation.SemanticModel =? methodSymbol.Parameters.[1]

    [<Test>]
    let ``returns correct named parameter symbol`` () =
        let compilation = TestCompilation "class X { void M() { N(j: 1, i: 2); } void N(int i, int j) {} }"
        let methodM = compilation.FindMethodDeclaration "X" "M"
        let methodSymbol = compilation.FindMethodSymbol "X" "N"
        let argument1 = methodM.Descendants<ArgumentSyntax>().First ()
        let argument2 = methodM.Descendants<ArgumentSyntax>().Skip(1).Single ()

        argument1.GetParameterSymbol compilation.SemanticModel =? methodSymbol.Parameters.[1]
        argument2.GetParameterSymbol compilation.SemanticModel =? methodSymbol.Parameters.[0]

    [<Test>]
    let ``returns correct params parameter symbol`` () =
        let compilation = TestCompilation "class X { void M() { N(1, 2, 3); } void N(int i, params int[] j) {} }"
        let methodM = compilation.FindMethodDeclaration "X" "M"
        let methodSymbol = compilation.FindMethodSymbol "X" "N"
        let argument1 = methodM.Descendants<ArgumentSyntax>().First ()
        let argument2 = methodM.Descendants<ArgumentSyntax>().Skip(1).First ()
        let argument3 = methodM.Descendants<ArgumentSyntax>().Skip(2).Single ()

        argument1.GetParameterSymbol compilation.SemanticModel =? methodSymbol.Parameters.[0]
        argument2.GetParameterSymbol compilation.SemanticModel =? methodSymbol.Parameters.[1]
        argument3.GetParameterSymbol compilation.SemanticModel =? methodSymbol.Parameters.[1]
