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
	using Roslyn.Syntax;

	/// <summary>
	///     Replaces all compound assignments by simple assignments with the appropriate expression. The C# specification states
	///     that a compound assignment of the form <c>x op= y</c> is evaluated as <c>x = x op y</c>, expect that x is evaluated only
	///     once. The fact that x is evaluated only once is important in regular C# code; for instance, consider <c>M()[0] += 1</c>,
	///     where M is a function returning an integer array. If M() returns a different array for each invocation, the difference
	///     between evaluating M() once or twice when processing the compound assignment might be observable. Within components of
	///     SafetySharp models, however, we only ever allow assignments to fields, locals, and paramaters of primitive types, such
	///     as int, bool, or decimal while arrays and structs are immutable and therefore cannot be assigned to at all. This
	///     simplifies the normalization of compound assignments, as we don't have to ensure that the expression on the left hand
	///     side of the assignment is evaluated only once.
	/// 
	///     For example, compound assignments such as <c>x += 1</c> or <c>y -= x + 1</c> are normalized to <c>x = x + (1)</c> and
	///     <c>y = y - (x + 1)</c>, respectively.
	/// </summary>
	public class CompoundAssignmentNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public CompoundAssignmentNormalizer()
			: base(NormalizationScope.ComponentStatements)
		{
		}

		/// <summary>
		///     Normalizes the <paramref name="expression" />, if it represents a compound assignment.
		/// </summary>
		public override SyntaxNode VisitBinaryExpression(BinaryExpressionSyntax expression)
		{
			SyntaxKind expressionKind;
			switch (expression.CSharpKind())
			{
				case SyntaxKind.AddAssignmentExpression:
					expressionKind = SyntaxKind.AddExpression;
					break;
				case SyntaxKind.SubtractAssignmentExpression:
					expressionKind = SyntaxKind.SubtractExpression;
					break;
				case SyntaxKind.MultiplyAssignmentExpression:
					expressionKind = SyntaxKind.MultiplyExpression;
					break;
				case SyntaxKind.DivideAssignmentExpression:
					expressionKind = SyntaxKind.DivideExpression;
					break;
				case SyntaxKind.ModuloAssignmentExpression:
					expressionKind = SyntaxKind.ModuloExpression;
					break;
				case SyntaxKind.AndAssignmentExpression:
					expressionKind = SyntaxKind.LogicalAndExpression;
					break;
				case SyntaxKind.ExclusiveOrAssignmentExpression:
					expressionKind = SyntaxKind.ExclusiveOrExpression;
					break;
				case SyntaxKind.OrAssignmentExpression:
					expressionKind = SyntaxKind.LogicalOrExpression;
					break;
				case SyntaxKind.LeftShiftAssignmentExpression:
					expressionKind = SyntaxKind.LeftShiftExpression;
					break;
				case SyntaxKind.RightShiftAssignmentExpression:
					expressionKind = SyntaxKind.RightShiftExpression;
					break;
				default:
					return expression;
			}

			var originalRightHand = (ExpressionSyntax)base.Visit(expression.Right);
			var parenthesizedExpression = SyntaxFactory.ParenthesizedExpression(originalRightHand).WithLeadingSpace();
			var rightHandExpression = SyntaxFactory.BinaryExpression(expressionKind, expression.Left.WithLeadingSpace(), parenthesizedExpression);
			var simpleAssignment = SyntaxFactory.BinaryExpression(SyntaxKind.SimpleAssignmentExpression, expression.Left, rightHandExpression);
			return simpleAssignment.WithTrivia(expression);
		}
	}
}