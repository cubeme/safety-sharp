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

namespace SafetySharp.CSharpCompiler.Normalization
{
	using System;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Roslyn;
	using Roslyn.Symbols;

	/// <summary>
	///     Replaces all uses of the ternary conditional operator <c>e ? e1 : e2</c> where <c>e1</c> and <c>e2</c> are of type
	///     <c>bool</c> with the semantically equivalent expression <c>(e && e1) || (!e && e2)</c>.
	/// </summary>
	public class BooleanConditionalNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public BooleanConditionalNormalizer()
			: base(NormalizationScope.ComponentStatements)
		{
		}

		/// <summary>
		///     Normalizes the conditional expression if both subexpressions are of type <c>bool</c>.
		/// </summary>
		/// <param name="expression">The conditional expression that should be normalized.</param>
		public override SyntaxNode VisitConditionalExpression(ConditionalExpressionSyntax expression)
		{
			var trueType = SemanticModel.GetTypeInfo(expression.WhenTrue).ConvertedType;
			var falseType = SemanticModel.GetTypeInfo(expression.WhenFalse).ConvertedType;
			var booleanSymbol = SemanticModel.GetTypeSymbol<bool>();

			if (!Equals(trueType, booleanSymbol) || !Equals(falseType, booleanSymbol))
				return expression;

			var condition = SyntaxFactory.ParenthesizedExpression(expression.Condition);
			var negatedCondition = SyntaxFactory.PrefixUnaryExpression(SyntaxKind.LogicalNotExpression, condition);
			var whenTrue = SyntaxFactory.ParenthesizedExpression(expression.WhenTrue);
			var whenFalse = SyntaxFactory.ParenthesizedExpression(expression.WhenFalse);

			var left = SyntaxFactory.BinaryExpression(SyntaxKind.LogicalAndExpression, condition, whenTrue);
			var right = SyntaxFactory.BinaryExpression(SyntaxKind.LogicalAndExpression, negatedCondition, whenFalse);

			var leftExpression = SyntaxFactory.ParenthesizedExpression(left);
			var rightExpression = SyntaxFactory.ParenthesizedExpression(right);

			return SyntaxFactory.BinaryExpression(SyntaxKind.LogicalOrExpression, leftExpression, rightExpression).NormalizeWhitespace();
		}
	}
}