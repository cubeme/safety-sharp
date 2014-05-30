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

namespace SafetySharp.CSharp.Transformation
{
	using System;
	using Metamodel;
	using Metamodel.Expressions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Utilities;

	/// <summary>
	///     Transforms a lowered C# syntax tree of an expression into a corresponding metamodel expression tree.
	/// </summary>
	internal class ExpressionTransformation : CSharpSyntaxVisitor<MetamodelElement>
	{
		/// <summary>
		///     Initializes a new instance of the <see cref="ExpressionTransformation" /> type.
		/// </summary>
		/// <param name="semanticModel">The semantic model that should be used to retrieve semantic information about the C# program.</param>
		/// <param name="symbolMap">The symbol map that should be used to look up metamodel element references for C# symbols.</param>
		internal ExpressionTransformation(SemanticModel semanticModel, SymbolMap symbolMap)
		{
			Argument.NotNull(semanticModel, () => semanticModel);
			Argument.NotNull(symbolMap, () => symbolMap);

			SemanticModel = semanticModel;
			SymbolMap = symbolMap;
		}

		/// <summary>
		///     Gets the semantic model that can be used to retrieve semantic information about the C# program.
		/// </summary>
		protected SemanticModel SemanticModel { get; private set; }

		/// <summary>
		///     Gets the symbol map that can be used to look up metamodel element references for C# symbols.
		/// </summary>
		protected SymbolMap SymbolMap { get; private set; }

		/// <summary>
		///     Transforms the C# <paramref name="expression" /> to a metamodel <see cref="Expression" />.
		/// </summary>
		/// <param name="expression">The C# expression that should be transformed.</param>
		public Expression Transform(ExpressionSyntax expression)
		{
			return (Expression)Visit(expression);
		}

		/// <summary>
		///     Raises an exception for all unsupported C# features found in the lowered C# syntax tree.
		/// </summary>
		/// <param name="node">The syntax node of the unsupported C# feature.</param>
		public override MetamodelElement DefaultVisit(SyntaxNode node)
		{
			Assert.NotReached("Encountered an unexpected C# syntax node: '{0}'.", node.CSharpKind());
			return null;
		}

		/// <summary>
		///     Transforms a C# identifier name to the corresponding metamodel expression.
		/// </summary>
		/// <param name="node">The C# identifier name that should be transformed.</param>
		public override MetamodelElement VisitIdentifierName(IdentifierNameSyntax node)
		{
			var symbolInfo = SemanticModel.GetSymbolInfo(node);
			var symbol = symbolInfo.Symbol;

			Assert.NotNull(symbol, "Unable to determine symbol for identifier '{0}'.", node);

			var fieldSymbol = symbol as IFieldSymbol;
			if (fieldSymbol != null)
				return new FieldAccessExpression(SymbolMap.GetFieldReference(fieldSymbol));

			Assert.NotReached("Unexpected C# symbol type: '{0}'", symbol.GetType().FullName);
			return null;
		}

		/// <summary>
		///     Transforms a C# unary expression to the corresponding metamodel unary expression.
		/// </summary>
		/// <param name="node">The C# unary expression that should be transformed.</param>
		public override MetamodelElement VisitPrefixUnaryExpression(PrefixUnaryExpressionSyntax node)
		{
			var operand = (Expression)Visit(node.Operand);

			switch (node.CSharpKind())
			{
				case SyntaxKind.UnaryPlusExpression:
					return operand;
				case SyntaxKind.UnaryMinusExpression:
					return new UnaryExpression(operand, UnaryOperator.Minus);
				case SyntaxKind.LogicalNotExpression:
					return new UnaryExpression(operand, UnaryOperator.LogicalNot);
				default:
					Assert.NotReached("Unsupported unary C# operator: '{0}'.", node.CSharpKind());
					return null;
			}
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
		/// <param name="node">The C# expression that should be transformed.</param>
		public override MetamodelElement VisitParenthesizedExpression(ParenthesizedExpressionSyntax node)
		{
			return Visit(node.Expression);
		}

		/// <summary>
		///     Transforms a C# literal to the corresponding metamodel literal.
		/// </summary>
		/// <param name="node"></param>
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
		///     Maps the C# syntax kind to the corresponding binary operator.
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
					Assert.NotReached("Unsupported binary C# operator: '{0}'.", syntaxKind);
					return 0;
			}
		}
	}
}