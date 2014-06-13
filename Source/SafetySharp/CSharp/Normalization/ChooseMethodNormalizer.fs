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
open SafetySharp.CSharp.Extensions

/// Normalizes all usages of the nondeterministic Choose methods.
type ChooseMethodNormalizer () =
    inherit CSharpNormalizer ()

    override this.VisitBinaryExpression (expression : BinaryExpressionSyntax) =
        if expression.CSharpKind () <> SyntaxKind.SimpleAssignmentExpression then
            upcast expression
        else if expression.Right.CSharpKind () <> SyntaxKind.InvocationExpression then
            upcast expression
        else
            let invocation = (expression.Right :?> InvocationExpressionSyntax)
            let methodSymbol = this.semanticModel.GetSymbolInfo(invocation).Symbol :?> IMethodSymbol

            if methodSymbol = null then
                sprintf "Unable to determine symbol of invocation '%A'." invocation |> invalidOp

            if methodSymbol = this.semanticModel.GetChooseBooleanMethodSymbol false then
                upcast SyntaxFactory.ParseExpression(sprintf "Choose.Boolean(out %A)" expression.Left)
                    .WithLeadingTrivia(expression.GetLeadingTrivia ())
                    .WithTrailingTrivia(expression.GetTrailingTrivia ())
            else
                upcast expression