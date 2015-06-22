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

namespace SafetySharp.Compiler.Normalization
{
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Editing;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;
	using Runtime;
	using Utilities;

	public class SideEffectsNormalizer : SyntaxNormalizer
	{
		private readonly Rewriter _rewriter = new Rewriter();

		/// <summary>
		///     Normalizes the <paramref name="methodDeclaration" />.
		/// </summary>
		/// <param name="methodDeclaration">The method declaration that should be normalized.</param>
		public override SyntaxNode VisitMethodDeclaration(MethodDeclarationSyntax methodDeclaration)
		{
			var methodSymbol = methodDeclaration.GetMethodSymbol(SemanticModel);

			if (!methodSymbol.IsProvidedPort(Compilation) && !methodSymbol.IsUpdateMethod(Compilation))
				return methodDeclaration;

			return methodDeclaration.WithBody(null);//(BlockSyntax)_rewriter.Visit(methodDeclaration.Body));
		}

		private class Rewriter : CSharpSyntaxWalker
		{
			private readonly SideEffectAnalyzer _analyzer;
			private readonly SemanticModel _semanticModel;
			private readonly SyntaxGenerator _syntax;
			private NameScope _nameScope;
			private SyntaxNode _result;
			private List<SyntaxNode> _statements = new List<SyntaxNode>();

			public StatementSyntax Rewrite(SyntaxNode methodBody)
			{
				_statements.Clear();
				_result = null;
				_nameScope = new NameScope();

				Visit(methodBody);
				// TODO: Wrap expression body in return
				return SyntaxFactory.Block(_statements.Cast<StatementSyntax>());
			}

			private SyntaxNode MakeTemporaryVariable()
			{
				return _result = _syntax.IdentifierName(_nameScope.MakeUnique("t"));
			}

			public override void VisitPostfixUnaryExpression(PostfixUnaryExpressionSyntax node)
			{
				Visit(node.Operand);

				switch (node.Kind())
				{
					case SyntaxKind.PostIncrementExpression:
						MakeTemporaryVariable();
						AddExpressionStatement(_syntax.AssignmentStatement(_result, node.Operand));
						AddExpressionStatement(_syntax.AssignmentStatement(node.Operand, _syntax.AddExpression(node.Operand, _syntax.LiteralExpression(1))));
						break;
					case SyntaxKind.PostDecrementExpression:
						MakeTemporaryVariable();
						AddExpressionStatement(_syntax.AssignmentStatement(_result, node.Operand));
						AddExpressionStatement(_syntax.AssignmentStatement(node.Operand,
							_syntax.SubtractExpression(node.Operand, _syntax.LiteralExpression(1))));
						break;
					default:
						Assert.NotReached("Encountered an unexpected unary operator: {0}.", node.Kind());
						break;
				}
			}

			public override void VisitLiteralExpression(LiteralExpressionSyntax node)
			{
				_result = node;
			}

			public override void VisitPrefixUnaryExpression(PrefixUnaryExpressionSyntax node)
			{
				if (_analyzer.IsSideEffectFree(node))
					_result = node;
				else
				{
					Visit(node.Operand);

					switch (node.Kind())
					{
						case SyntaxKind.UnaryPlusExpression:
						case SyntaxKind.UnaryMinusExpression:
						case SyntaxKind.BitwiseNotExpression:
						case SyntaxKind.LogicalNotExpression:
							var symbol = _semanticModel.GetSymbolInfo(node).Symbol as IMethodSymbol;
							Assert.NotNull(symbol, "Expected a valid method symbol.");

							if (!symbol.IsBuiltInOperator(_semanticModel))
							{
								AddExpressionStatement(node.WithOperand((ExpressionSyntax)_result));
							}
							else
								_result = node.WithOperand((ExpressionSyntax)_result);
							break;
						case SyntaxKind.PreIncrementExpression:
							AddExpressionStatement(_syntax.AssignmentStatement(node.Operand, _syntax.AddExpression(node.Operand, _syntax.LiteralExpression(1))));
							_result = node.Operand;
							break;
						case SyntaxKind.PreDecrementExpression:
							AddExpressionStatement(_syntax.AssignmentStatement(node.Operand,
								_syntax.SubtractExpression(node.Operand, _syntax.LiteralExpression(1))));
							_result = node.Operand;
							break;
						default:
							Assert.NotReached("Encountered an unexpected unary operator: {0}.", node.Kind());
							break;
					}
				}
			}

			private void AddExpressionStatement(SyntaxNode expression)
			{
				_statements.Add((StatementSyntax)_syntax.ExpressionStatement(expression));
			}

			public override void VisitBinaryExpression(BinaryExpressionSyntax node)
			{
				if (_analyzer.IsSideEffectFree(node))
					_result = node;
				else
				{
					var statements = _statements.ToList();

					_statements.Clear();
					Visit(node.Left);
					var t1 = (ExpressionSyntax)_result;
					var s1 = _statements.ToArray();

					_statements.Clear();
					Visit(node.Right);
					var t2 = (ExpressionSyntax)_result;
					var s2 = _statements.ToArray();

					_statements = statements;

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

							if (!symbol.IsBuiltInOperator(_semanticModel))
							{
								// TODO
							}
							else
							{
								_result = SyntaxFactory.BinaryExpression(node.Kind(), t1, t2);
								_statements.AddRange(s1);
								_statements.AddRange(s2);
							}
							break;
						case SyntaxKind.LogicalOrExpression:
							var tmp1 = MakeTemporaryVariable();

							_statements.AddRange(s1);
							_statements.Add((StatementSyntax)_syntax.IfStatement(t1,
								new[] { _syntax.AssignmentStatement(tmp1, _syntax.TrueLiteralExpression()) },
								s2.Concat(new[] { _syntax.AssignmentStatement(tmp1, t2) })));
							_result = tmp1;
							break;
						case SyntaxKind.LogicalAndExpression:
							var tmp2 = MakeTemporaryVariable();

							_statements.AddRange(s1);
							_statements.Add((StatementSyntax)_syntax.IfStatement(t1,
								s2.Concat(new[] { _syntax.AssignmentStatement(tmp2, t2) }),
								new[] { _syntax.AssignmentStatement(tmp2, _syntax.FalseLiteralExpression()) }));
							_result = tmp2;
							break;
						default:
							Assert.NotReached("Encountered an unexpected binary operator: {0}.", node.Kind());
							return;
					}
				}
			}

			public override void VisitAssignmentExpression(AssignmentExpressionSyntax node)
			{
				Visit(node.Right);
				AddExpressionStatement(node.WithRight((ExpressionSyntax)_result));
			}

			public override void VisitIfStatement(IfStatementSyntax node)
			{
				Visit(node.Condition);
				var condition = _result;

				var statements = _statements.ToList();
				_statements.Clear();

				Visit(node.Statement);
				var thenStatements = _statements.ToArray();

				_statements.Clear();
				Visit(node.Else);
				var elseStatements = _statements.ToArray();

				_statements = statements;
				_statements.Add(_syntax.IfStatement(condition, thenStatements, node.Else == null ? null : elseStatements));
			}

			public override void VisitIdentifierName(IdentifierNameSyntax node)
			{
				if (_analyzer.IsSideEffectFree(node))
					_result = node;
				else
					AddExpressionStatement(_syntax.AssignmentStatement(MakeTemporaryVariable(), node));
			}

			public override void VisitReturnStatement(ReturnStatementSyntax node)
			{
				if (node.Expression == null || _analyzer.IsSideEffectFree(node.Expression))
					_statements.Add(node);
				else
				{
					Visit(node.Expression);
					_statements.Add(_syntax.ReturnStatement(_result));
				}
			}
		}
	}
}