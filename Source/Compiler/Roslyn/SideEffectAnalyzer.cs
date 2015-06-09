// The MIT License (MIT)
// 
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

namespace SafetySharp.Compiler.Roslyn
{
	using System;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Symbols;
	using Utilities;

	/// <summary>
	///     Analyzes an expression to determine whether it has potential side effects or whether it is guaranteed to be
	///     side effect free. For instance:
	///     - 1 + 1: Side effect free
	///     - x + y: Potential side effect for variables of user-defined type with an overloaded + operator
	///     - f()  : Potential side effect
	///     - ++x  : Not side effect free
	/// </summary>
	public class SideEffectAnalyzer
	{
		/// <summary>
		///     The visitor instance that is used to analyze expressions for side effects.
		/// </summary>
		private readonly Visitor _visitor;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="semanticModel">The <see cref="SemanticModel" /> that should be used to check for overloaded operators.</param>
		public SideEffectAnalyzer(SemanticModel semanticModel)
		{
			Requires.NotNull(semanticModel, () => semanticModel);
			_visitor = new Visitor(semanticModel);
		}

		/// <summary>
		///     Determines whether the <paramref name="expression" /> is side effect free. If <c>false</c> is returned,
		///     <paramref name="expression" /> has at least one potential side effect.
		/// </summary>
		/// <param name="expression">The <see cref="ExpressionSyntax" /> that should be analyzed.</param>
		public bool IsSideEffectFree(ExpressionSyntax expression)
		{
			Requires.NotNull(expression, () => expression);
			return _visitor.Visit(expression);
		}

		/// <summary>
		///     Visits all kinds of expressions and determines whether they are side effect free. The visitor returns <c>true</c> to
		///     indicate that the analyzed expression is side effect free.
		/// </summary>
		private class Visitor : CSharpSyntaxVisitor<bool>
		{
			private readonly SemanticModel _semanticModel;

			public Visitor(SemanticModel semanticModel)
			{
				_semanticModel = semanticModel;
			}

			public override bool DefaultVisit(SyntaxNode node)
			{
				Assert.NotReached("Encountered an unexpected kind of syntax node: {0}.", node.Kind());
				return false;
			}

			public override bool VisitLiteralExpression(LiteralExpressionSyntax node)
			{
				return true;
			}

			public override bool VisitIdentifierName(IdentifierNameSyntax node)
			{
				var symbol = _semanticModel.GetSymbolInfo(node).Symbol;
				Assert.NotNull(symbol, "Expected a valid symbol.");

				if (symbol is ILocalSymbol || symbol is IFieldSymbol)
					return true;

				return false;
			}

			public override bool VisitPrefixUnaryExpression(PrefixUnaryExpressionSyntax node)
			{
				switch (node.Kind())
				{
					case SyntaxKind.UnaryPlusExpression:
					case SyntaxKind.UnaryMinusExpression:
					case SyntaxKind.BitwiseNotExpression:
					case SyntaxKind.LogicalNotExpression:
						var symbol = _semanticModel.GetSymbolInfo(node).Symbol as IMethodSymbol;
						Assert.NotNull(symbol, "Expected a valid method symbol.");

						if (symbol.IsBuiltInOperator(_semanticModel))
							return Visit(node.Operand);

						return false;
					case SyntaxKind.PreIncrementExpression:
					case SyntaxKind.PreDecrementExpression:
						return false;
					default:
						Assert.NotReached("Encountered an unexpected unary operator: {0}.", node.Kind());
						return false;
				}
			}

			public override bool VisitPostfixUnaryExpression(PostfixUnaryExpressionSyntax node)
			{
				switch (node.Kind())
				{
					case SyntaxKind.PostIncrementExpression:
					case SyntaxKind.PostDecrementExpression:
						return false;
					default:
						Assert.NotReached("Encountered an unexpected unary operator: {0}.", node.Kind());
						return false;
				}
			}

			public override bool VisitBinaryExpression(BinaryExpressionSyntax node)
			{
				switch (node.Kind())
				{
					case SyntaxKind.AddExpression:
					case SyntaxKind.SubtractExpression:
					case SyntaxKind.MultiplyExpression:
					case SyntaxKind.DivideExpression:
					case SyntaxKind.ModuloExpression:
					case SyntaxKind.LeftShiftExpression:
					case SyntaxKind.RightShiftExpression:
					case SyntaxKind.BitwiseOrExpression:
					case SyntaxKind.BitwiseAndExpression:
					case SyntaxKind.ExclusiveOrExpression:
					case SyntaxKind.EqualsExpression:
					case SyntaxKind.NotEqualsExpression:
					case SyntaxKind.LessThanExpression:
					case SyntaxKind.LessThanOrEqualExpression:
					case SyntaxKind.GreaterThanExpression:
					case SyntaxKind.GreaterThanOrEqualExpression:
						var symbol = _semanticModel.GetSymbolInfo(node).Symbol as IMethodSymbol;
						Assert.NotNull(symbol, "Expected a valid method symbol.");

						if (symbol.IsBuiltInOperator(_semanticModel))
							return Visit(node.Left) && Visit(node.Right);

						return false;
					case SyntaxKind.LogicalOrExpression:
					case SyntaxKind.LogicalAndExpression:
						// Roslyn doesn't provide a symbol for operators && and || for built-in types.
						// see also: https://roslyn.codeplex.com/workitem/327
						var leftType = _semanticModel.GetTypeInfo(node.Left).Type;
						var rightType = _semanticModel.GetTypeInfo(node.Left).Type;

						if (leftType.IsBuiltType(_semanticModel) && rightType.IsBuiltType(_semanticModel))
							return Visit(node.Left) && Visit(node.Right);

						goto case SyntaxKind.AddExpression;
					default:
						Assert.NotReached("Encountered an unexpected binary operator: {0}.", node.Kind());
						return false;
				}
			}

			public override bool VisitAssignmentExpression(AssignmentExpressionSyntax node)
			{
				return false;
			}

			public override bool VisitMemberAccessExpression(MemberAccessExpressionSyntax node)
			{
				return Visit(node.Name) && Visit(node.Expression);
			}

			public override bool VisitParenthesizedExpression(ParenthesizedExpressionSyntax node)
			{
				return Visit(node.Expression);
			}

			public override bool VisitInvocationExpression(InvocationExpressionSyntax node)
			{
				return false;
			}

			public override bool VisitThisExpression(ThisExpressionSyntax node)
			{
				return true;
			}

			public override bool VisitBaseExpression(BaseExpressionSyntax node)
			{
				return true;
			}

			public override bool VisitElementAccessExpression(ElementAccessExpressionSyntax node)
			{
				var symbol = _semanticModel.GetSymbolInfo(node).Symbol as IPropertySymbol;

				// If we get a symbol, this element access refers to a user-defined indexer. Always assume side effects.
				if (symbol != null)
					return false;

				// Otherwise, it is an array access, which is considered to be side effect free.
				return true;
			}

			public override bool VisitCastExpression(CastExpressionSyntax node)
			{
				var symbol = _semanticModel.GetSymbolInfo(node).Symbol as IMethodSymbol;

				// If we get a symbol, this cast is a user-defined conversion. Always assume side effects.
				if (symbol != null)
					return false;

				// Otherwise, it is a built-in conversion, which is considered to be side effect free.
				return true;
			}

			public override bool VisitObjectCreationExpression(ObjectCreationExpressionSyntax node)
			{
				return false;
			}
		}
	}
}