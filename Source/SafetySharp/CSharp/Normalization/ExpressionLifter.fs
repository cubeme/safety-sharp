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
open SafetySharp.Modeling

/// Lifts all method invocation parameter expressions 'expr' to a lambda function of the form '() => expr'.
type ExpressionLifter () =
    inherit CSharpNormalizer ()

    override this.VisitArgument node =
        let requiresRewrite = node.ParameterHasAttribute<LiftExpressionAttribute> this.semanticModel
        let node = base.VisitArgument node :?> ArgumentSyntax

        if not requiresRewrite then
            upcast node
        else
            let expression = SyntaxFactory.ParenthesizedLambdaExpression(node.Expression.WithLeadingTrivia().WithTrailingTrivia())
            let arrowToken = expression.ArrowToken.WithLeadingTrivia(SyntaxFactory.Space).WithTrailingTrivia(SyntaxFactory.Space)
            let expression = expression.WithArrowToken(arrowToken)
            let expression = expression.WithLeadingTrivia(node.Expression.GetLeadingTrivia ())
            let expression = expression.WithTrailingTrivia(node.Expression.GetTrailingTrivia ())
            
            let node = node.WithExpression expression
            upcast node