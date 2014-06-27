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

namespace SafetySharp.CSharp.Normalization

open System
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp.Roslyn
open SafetySharp.Utilities
open SafetySharp.Modeling

/// Normalizes all usages of the nondeterministic Choose methods.
type ChooseMethodNormalizer () =
    inherit CSharpNormalizer (NormalizationScope.Components)

    override this.VisitBinaryExpression node =
        if node.CSharpKind () <> SyntaxKind.SimpleAssignmentExpression then
            upcast node
        elif node.Right.CSharpKind () <> SyntaxKind.InvocationExpression then
            upcast node
        else
            let invocation = node.Right :?> InvocationExpressionSyntax
            let methodSymbol = this.semanticModel.GetSymbol<IMethodSymbol> invocation

            if methodSymbol.ContainingType = this.semanticModel.GetTypeSymbol<Choose> () then
                let outToken = SyntaxFactory.Token(SyntaxKind.OutKeyword)
                let argument = SyntaxFactory.Argument(node.Left).WithRefOrOutKeyword outToken
                let arguments = invocation.ArgumentList.Arguments.Insert (0, argument)
                let argumentList = invocation.ArgumentList.WithArguments arguments
                let invocation = invocation.WithArgumentList argumentList
                upcast (invocation.NormalizeWhitespace () |> Syntax.WithTriviaFromNode node)
            else
                upcast node