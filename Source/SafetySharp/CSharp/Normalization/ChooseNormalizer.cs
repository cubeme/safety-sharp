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
{
	using System;
	using Extensions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Utilities;

	/// <summary>
	///     Normalizes all usages of the nondeterministic selection methods.
	/// </summary>
	internal class ChooseNormalizer : CSharpNormalizer
	{
		public override SyntaxNode VisitBinaryExpression(BinaryExpressionSyntax node)
		{
			if (node.CSharpKind() != SyntaxKind.SimpleAssignmentExpression)
				return node;

			if (node.Right.CSharpKind() != SyntaxKind.InvocationExpression)
				return node;

			var invocation = (InvocationExpressionSyntax)node.Right;
			var methodSymbol = (IMethodSymbol)SemanticModel.GetSymbolInfo(invocation).Symbol;
			Assert.NotNull(methodSymbol, "Unable to determine method symbol of invocation '{0}'.", invocation);

			if (!SemanticModel.GetChooseFromValuesMethodSymbol(normalizedMethod: false).Equals(methodSymbol.OriginalDefinition))
				return node;

			// TODO: What if node.Left is not a valid expression for an out parameter, i.e. variable declaration, etc.?
			var outExpression = SyntaxFactory.Argument(null, SyntaxFactory.Token(SyntaxKind.OutKeyword).WithTrailingTrivia(SyntaxFactory.Space), node.Left);
			var arguments = invocation.ArgumentList.Arguments.Insert(0, outExpression);
			var argumentList = SyntaxFactory.ArgumentList(arguments);
			return SyntaxFactory.InvocationExpression(SyntaxFactory.IdentifierName("Choose"), argumentList);
		}

		public override SyntaxNode VisitInvocationExpression(InvocationExpressionSyntax node)
		{
			var methodSymbol = (IMethodSymbol)SemanticModel.GetSymbolInfo(node).Symbol;
			Assert.NotNull(methodSymbol, "Unable to determine method symbol of invocation '{0}'.", node);

			if (SemanticModel.GetChooseFromValuesMethodSymbol(normalizedMethod: false).Equals(methodSymbol.OriginalDefinition))
				Assert.NotReached("Unsupported use of Choose function.");

			return base.VisitInvocationExpression(node);
		}
	}
}