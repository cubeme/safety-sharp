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

namespace SafetySharp.CSharp
{
	using System;
	using Metamodel;
	using Metamodel.Expressions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Utilities;

	internal partial class TransformationVisitor
	{
		/// <summary>
		///     Transforms a C# unary expression to the corresponding metamodel unary expression.
		/// </summary>
		/// <param name="node">The C# unary expression that should be transformed.</param>
		public override MetamodelElement VisitPrefixUnaryExpression(PrefixUnaryExpressionSyntax node)
		{
			return new UnaryExpression((Expression)Visit(node.Operand), MapUnaryOperator(node.CSharpKind()));
		}

		/// <summary>
		///     Transforms a C# binary expression to the corresponding metamodel binary expression.
		/// </summary>
		/// <param name="node">The C# binary expression that should be transformed.</param>
		public override MetamodelElement VisitBinaryExpression(BinaryExpressionSyntax node)
		{
			var left = (Expression)Visit(node.Left);
			var right = (Expression)Visit(node.Right);

			return new BinaryExpression(left, MapBinaryOperator(node.CSharpKind()), right);
		}

		/// <summary>
		///     Skips over a C# parenthesized expression.
		/// </summary>
		public override MetamodelElement VisitParenthesizedExpression(ParenthesizedExpressionSyntax node)
		{
			return Visit(node.Expression);
		}

		/// <summary>
		///     Transforms a C# literal to the corresponding metamodel literal.
		/// </summary>
		/// <param name="node"></param>
		/// <returns></returns>
		public override MetamodelElement VisitLiteralExpression(LiteralExpressionSyntax node)
		{
			switch (node.Token.CSharpKind())
			{
				case SyntaxKind.TrueKeyword:
					return BooleanLiteral.True;
				case SyntaxKind.FalseKeyword:
					return BooleanLiteral.False;
				case SyntaxKind.NumericLiteralToken:
					if (node.Token.Value is int)
						return new IntegerLiteral((int)node.Token.Value);

					if (node.Token.Value is decimal)
						return new DecimalLiteral((decimal)node.Token.Value);

					Assert.NotReached("Numeric literals of type '{0}' are not supported.", node.Token.Value.GetType().FullName);
					return null;
				default:
					Assert.NotReached("Unsupported C# literal: '{0}'.", node.Token.CSharpKind());
					return null;
			}
		}

		/// <summary>
		///     Maps the C# syntax to the corresponding unary operator.
		/// </summary>
		/// <param name="syntaxKind">The syntax kind that should be mapped.</param>
		private static UnaryOperator MapUnaryOperator(SyntaxKind syntaxKind)
		{
			switch (syntaxKind)
			{
				case SyntaxKind.UnaryPlusExpression:
					return UnaryOperator.Plus;
				case SyntaxKind.UnaryMinusExpression:
					return UnaryOperator.Minus;
				case SyntaxKind.LogicalNotExpression:
					return UnaryOperator.LogicalNot;
				default:
					Assert.NotReached("Unsupported C# unary operator: '{0}'.", syntaxKind);
					return 0;
			}
		}

		/// <summary>
		///     Maps the C# syntax to the corresponding binary operator.
		/// </summary>
		/// <param name="syntaxKind">The syntax kind that should be mapped.</param>
		private static BinaryOperator MapBinaryOperator(SyntaxKind syntaxKind)
		{
			switch (syntaxKind)
			{
				case SyntaxKind.AddExpression:
					return BinaryOperator.Add;
				case SyntaxKind.SubtractExpression:
					return BinaryOperator.Subtract;
				case SyntaxKind.MultiplyExpression:
					return BinaryOperator.Multiply;
				case SyntaxKind.DivideExpression:
					return BinaryOperator.Divide;
				case SyntaxKind.ModuloExpression:
					return BinaryOperator.Modulo;
				case SyntaxKind.LogicalAndExpression:
					return BinaryOperator.LogicalAnd;
				case SyntaxKind.LogicalOrExpression:
					return BinaryOperator.LogicalOr;
				case SyntaxKind.EqualsExpression:
					return BinaryOperator.Equals;
				case SyntaxKind.NotEqualsExpression:
					return BinaryOperator.NotEquals;
				case SyntaxKind.LessThanExpression:
					return BinaryOperator.LessThan;
				case SyntaxKind.LessThanOrEqualExpression:
					return BinaryOperator.LessThanOrEqual;
				case SyntaxKind.GreaterThanExpression:
					return BinaryOperator.GreaterThan;
				case SyntaxKind.GreaterThanOrEqualExpression:
					return BinaryOperator.GreaterThanOrEqual;
				default:
					Assert.NotReached("Unsupported C# binary operator: '{0}'.", syntaxKind);
					return 0;
			}
		}
	}
}