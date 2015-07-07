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

namespace SafetySharp.Compiler.Normalization.BoundTree
{
	using System;
	using System.Collections.Generic;
	using System.Collections.Immutable;
	using System.Linq;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Editing;
	using Modeling;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;
	using Utilities;

	/// <summary>
	///     Replaces all side-effecting expressions within the method bodies that metadata is generated for with semantically
	///     equivalent side-effect free versions.
	/// </summary>
	public sealed class SideEffectsNormalizer : BoundTreeNormalizer
	{
		/// <summary>
		///     Normalizes the <paramref name="methodDeclaration" />.
		/// </summary>
		protected override SyntaxNode Normalize(MethodDeclarationSyntax methodDeclaration)
		{
			var rewriter = new Rewriter(SemanticModel, Syntax);
			var transformedBody = rewriter.Rewrite(methodDeclaration);
			return methodDeclaration.WithExpressionBody(null).WithBody(transformedBody).NormalizeWhitespace();
		}

		/// <summary>
		///     Rewrites a method body.
		/// </summary>
		private class Rewriter : CSharpSyntaxVisitor<Rewriter.Result>
		{
			/// <summary>
			///     The analyzer that is used to check whether an expression has potential side effects.
			/// </summary>
			private readonly SideEffectAnalyzer _analyzer;

			/// <summary>
			///     The local variables generated during the rewrite.
			/// </summary>
			private readonly List<GeneratedVariable> _generatedVariables = new List<GeneratedVariable>();

			/// <summary>
			///     The semantic model that is used for semantic analysis of the method body.
			/// </summary>
			private readonly SemanticModel _semanticModel;

			/// <summary>
			///     The syntax generator that is used to generate the new method body code.
			/// </summary>
			private readonly SyntaxGenerator _syntax;

			/// <summary>
			///     The name scope that is used to generate unique names for generated variables.
			/// </summary>
			private NameScope _nameScope;

			/// <summary>
			///     Initializes a new instance.
			/// </summary>
			/// <param name="semanticModel">The semantic model that should be used for semantic analysis of the method body.</param>
			/// <param name="syntax">The syntax generator that should be used to generate the new method body code.</param>
			public Rewriter(SemanticModel semanticModel, SyntaxGenerator syntax)
			{
				_semanticModel = semanticModel;
				_syntax = syntax;
				_analyzer = new SideEffectAnalyzer(semanticModel);
			}

			/// <summary>
			///     Rewrites the <paramref name="methodDeclaration" />'s body.
			/// </summary>
			/// <param name="methodDeclaration">The method declaration that should be rewritten.</param>
			public BlockSyntax Rewrite(MethodDeclarationSyntax methodDeclaration)
			{
				_nameScope = methodDeclaration.GetNameScope(_semanticModel, includeLocals: true);

				var result = Visit(methodDeclaration.Body);
				var statements = result.Statements.ToArray();

				Assert.That(statements.Length == 1, "Expected a single block statement.");
				Assert.OfType<BlockSyntax>(statements[0]);

				var blockStatement = (BlockSyntax)statements[0];
				var updatedStatements = blockStatement.Statements.InsertRange(0, _generatedVariables.Select(
					variable => (StatementSyntax)_syntax.LocalDeclarationStatement(variable.Type, variable.Name)));

				return blockStatement.WithStatements(updatedStatements);
			}

			/// <summary>
			///     Rewrites the <paramref name="literal" />.
			/// </summary>
			public override Result VisitLiteralExpression(LiteralExpressionSyntax literal)
			{
				return new Result(literal);
			}

			/// <summary>
			///     Rewrites the <paramref name="identifier" />.
			/// </summary>
			public override Result VisitIdentifierName(IdentifierNameSyntax identifier)
			{
				if (_analyzer.IsSideEffectFree(identifier))
					return new Result(identifier);

				var symbol = identifier.GetReferencedSymbol(_semanticModel);
				switch (symbol.Kind)
				{
					case SymbolKind.Method:
						return Result.Default.WithExpression(identifier);
					case SymbolKind.Parameter:
					case SymbolKind.Field:
					case SymbolKind.Local:
					case SymbolKind.Property:
						var variable = GenerateVariable(identifier);
						return Result.Default.WithExpression(variable).WithExpressionStatement(_syntax.AssignmentStatement(variable.Identifier, identifier));
					default:
						Assert.NotReached("Unexpected symbol kind: '{0}' for identifier '{1}'.", symbol.Kind, identifier);
						return default(Result);
				}
			}

			/// <summary>
			///     Rewrites the <paramref name="expression" />.
			/// </summary>
			public override Result VisitThisExpression(ThisExpressionSyntax expression)
			{
				return new Result(expression);
			}

			/// <summary>
			///     Rewrites the <paramref name="expression" />.
			/// </summary>
			public override Result VisitBaseExpression(BaseExpressionSyntax expression)
			{
				return new Result(expression);
			}

			/// <summary>
			///     Rewrites the <paramref name="expression" />.
			/// </summary>
			public override Result VisitParenthesizedExpression(ParenthesizedExpressionSyntax expression)
			{
				var result = Visit(expression.Expression);
				return result.WithExpression(SyntaxFactory.ParenthesizedExpression(result.Expression));
			}

			/// <summary>
			///     Rewrites the <paramref name="unaryExpression" />.
			/// </summary>
			public override Result VisitPostfixUnaryExpression(PostfixUnaryExpressionSyntax unaryExpression)
			{
				var result = Visit(unaryExpression.Operand);
				var variable = GenerateVariable(unaryExpression);

				switch (unaryExpression.Kind())
				{
					case SyntaxKind.PostIncrementExpression:
						return result
							.WithExpressionStatement((ExpressionSyntax)_syntax.AssignmentStatement(variable.Identifier, result.Expression))
							.WithExpressionStatement((ExpressionSyntax)_syntax.AssignmentStatement(result.Expression,
								_syntax.AddExpression(result.Expression, _syntax.LiteralExpression(1))))
							.WithExpression(variable);
					case SyntaxKind.PostDecrementExpression:
						return result
							.WithExpressionStatement((ExpressionSyntax)_syntax.AssignmentStatement(variable.Identifier, result.Expression))
							.WithExpressionStatement((ExpressionSyntax)_syntax.AssignmentStatement(result.Expression,
								_syntax.SubtractExpression(result.Expression, _syntax.LiteralExpression(1))))
							.WithExpression(variable);
					default:
						Assert.NotReached("Encountered an unexpected unary operator: {0}.", unaryExpression.Kind());
						return default(Result);
				}
			}

			/// <summary>
			///     Rewrites the <paramref name="unaryExpression" />.
			/// </summary>
			public override Result VisitPrefixUnaryExpression(PrefixUnaryExpressionSyntax unaryExpression)
			{
				if (_analyzer.IsSideEffectFree(unaryExpression))
					return new Result(unaryExpression);

				var result = Visit(unaryExpression.Operand);

				switch (unaryExpression.Kind())
				{
					case SyntaxKind.UnaryPlusExpression:
					case SyntaxKind.UnaryMinusExpression:
					case SyntaxKind.BitwiseNotExpression:
					case SyntaxKind.LogicalNotExpression:
						var symbol = _semanticModel.GetSymbolInfo(unaryExpression).Symbol as IMethodSymbol;
						Assert.NotNull(symbol, "Expected a valid method symbol.");
						Assert.That(symbol.IsBuiltInOperator(), "Overloaded operators are not supported.");

						return result.WithExpression(unaryExpression.WithOperand(result.Expression));
					case SyntaxKind.PreIncrementExpression:
						return result
							.WithExpressionStatement(_syntax.AssignmentStatement(result.Expression,
								_syntax.AddExpression(result.Expression, _syntax.LiteralExpression(1))))
							.WithExpression(result.Expression);
					case SyntaxKind.PreDecrementExpression:
						return result
							.WithExpressionStatement(_syntax.AssignmentStatement(result.Expression,
								_syntax.SubtractExpression(result.Expression, _syntax.LiteralExpression(1))))
							.WithExpression(result.Expression);
					default:
						Assert.NotReached("Encountered an unexpected unary operator: {0}.", unaryExpression.Kind());
						return default(Result);
				}
			}

			/// <summary>
			///     Rewrites the <paramref name="binaryExpression" />.
			/// </summary>
			public override Result VisitBinaryExpression(BinaryExpressionSyntax binaryExpression)
			{
				if (_analyzer.IsSideEffectFree(binaryExpression))
					return new Result(binaryExpression);

				var leftResult = Visit(binaryExpression.Left);
				var rightResult = Visit(binaryExpression.Right);
				var leftVariable = GenerateVariable(binaryExpression.Left);
				var result = leftResult.WithExpressionStatement(_syntax.AssignmentStatement(leftVariable.Identifier, leftResult.Expression));

				switch (binaryExpression.Kind())
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
						var symbol = _semanticModel.GetSymbolInfo(binaryExpression).Symbol as IMethodSymbol;
						Assert.NotNull(symbol, "Expected a valid method symbol.");
						Requires.That(symbol.IsBuiltInOperator() || symbol.ContainingType.Equals(_semanticModel.GetTypeSymbol<State>()),
							"Overloaded operators are not supported.");

						return result
							.WithStatements(rightResult)
							.WithExpression(SyntaxFactory.BinaryExpression(binaryExpression.Kind(), leftVariable.Identifier, rightResult.Expression));

					case SyntaxKind.LogicalOrExpression:
						var orVariable = GenerateVariable(_semanticModel.GetTypeSymbol<bool>());

						return result
							.WithExpression(orVariable.Identifier)
							.WithStatement(_syntax.IfStatement(
								leftResult.Expression,
								new[] { _syntax.AssignmentStatement(orVariable.Identifier, _syntax.TrueLiteralExpression()) },
								rightResult.Statements.Concat(new[] { _syntax.AssignmentStatement(orVariable.Identifier, rightResult.Expression) })));

					case SyntaxKind.LogicalAndExpression:
						var andVariable = GenerateVariable(_semanticModel.GetTypeSymbol<bool>());

						return result
							.WithExpression(andVariable.Identifier)
							.WithStatement(_syntax.IfStatement(
								leftResult.Expression,
								rightResult.Statements.Concat(new[] { _syntax.AssignmentStatement(andVariable.Identifier, rightResult.Expression) }),
								new[] { _syntax.AssignmentStatement(andVariable.Identifier, _syntax.FalseLiteralExpression()) }));
					default:
						Assert.NotReached("Encountered an unexpected binary operator: {0}.", binaryExpression.Kind());
						return Result.Default;
				}
			}

			/// <summary>
			///     Rewrites the <paramref name="expression" />.
			/// </summary>
			public override Result VisitMemberAccessExpression(MemberAccessExpressionSyntax expression)
			{
				var symbol = expression.GetReferencedSymbol(_semanticModel);
				switch (symbol.Kind)
				{
					case SymbolKind.Field:
						if (symbol.ContainingType.TypeKind == TypeKind.Enum)
							return new Result(expression);
						goto default;
					case SymbolKind.Namespace:
						return Result.Default.WithExpression(expression);
					default:
						var result = Visit(expression.Expression);
						return result.WithExpression((ExpressionSyntax)_syntax.MemberAccessExpression(result.Expression, expression.Name));
				}
			}

			/// <summary>
			///     Rewrites the <paramref name="expression" />.
			/// </summary>
			public override Result VisitConditionalExpression(ConditionalExpressionSyntax expression)
			{
				if (_analyzer.IsSideEffectFree(expression))
					return new Result(expression);

				var conditionResult = Visit(expression.Condition);
				var trueResult = Visit(expression.WhenTrue);
				var falseResult = Visit(expression.WhenFalse);

				var variable = GenerateVariable(expression.WhenTrue);

				return new Result(variable.Identifier)
					.WithStatements(conditionResult)
					.WithStatement(_syntax.IfStatement(
						conditionResult.Expression,
						trueResult.Statements.Concat(new[] { _syntax.AssignmentStatement(variable.Identifier, trueResult.Expression) }),
						falseResult.Statements.Concat(new[] { _syntax.AssignmentStatement(variable.Identifier, falseResult.Expression) })));
			}

			/// <summary>
			///     Rewrites the <paramref name="assignment" />.
			/// </summary>
			public override Result VisitAssignmentExpression(AssignmentExpressionSyntax assignment)
			{
				Requires.That(assignment.Kind() == SyntaxKind.SimpleAssignmentExpression, "Unexpected compound assignment.");
				Requires.That(_analyzer.IsSideEffectFree(assignment.Left), "Left-hand side of assignment has side effect: '{0}'.", assignment);

				var result = Visit(assignment.Right);
				return result
					.WithExpressionStatement(_syntax.AssignmentStatement(assignment.Left, result.Expression))
					.WithExpression(assignment.Left);
			}

			/// <summary>
			///     Rewrites the <paramref name="invocation" />.
			/// </summary>
			public override Result VisitInvocationExpression(InvocationExpressionSyntax invocation)
			{
				var methodSymbol = invocation.GetReferencedSymbol<IMethodSymbol>(_semanticModel);
				var argumentResults = invocation.ArgumentList.Arguments.Select(
					argument =>
					{
						// Unfortunately, ArgumentSyntax does not derive from ExpressionSyntax
						var argumentResult = Visit(argument.Expression);
						return new { Statements = argumentResult.Statements, Argument = argument.WithExpression(argumentResult.Expression) };
					}).ToArray();

				var result = argumentResults.Aggregate(Visit(invocation.Expression), (r, argResult) => r.WithStatements(argResult.Statements));
				var transformedInvocation = _syntax.InvocationExpression(result.Expression, argumentResults.Select(argResult => argResult.Argument));

				if (methodSymbol.ReturnsVoid)
					return result.WithExpressionStatement(transformedInvocation).WithoutExpression();

				var variable = GenerateVariable(methodSymbol.ReturnType);
				return result.WithExpressionStatement(_syntax.AssignmentStatement(variable.Identifier, transformedInvocation)).WithExpression(variable);
			}

			/// <summary>
			///     Removes the <paramref name="statement" />.
			/// </summary>
			public override Result VisitEmptyStatement(EmptyStatementSyntax statement)
			{
				return Result.Default;
			}

			/// <summary>
			///     Rewrites the <paramref name="returnStatement" />.
			/// </summary>
			public override Result VisitReturnStatement(ReturnStatementSyntax returnStatement)
			{
				if (returnStatement.Expression == null || _analyzer.IsSideEffectFree(returnStatement.Expression))
					return new Result(returnStatement);

				var result = Visit(returnStatement.Expression);
				return result.WithStatement(_syntax.ReturnStatement(result.Expression)).WithoutExpression();
			}

			/// <summary>
			///     Rewrites the <paramref name="declaration" />.
			/// </summary>
			public override Result VisitLocalDeclarationStatement(LocalDeclarationStatementSyntax declaration)
			{
				var result = Result.Default;
				var type = declaration.Declaration.Type;

				foreach (var variable in declaration.Declaration.Variables)
				{
					if (variable.Initializer == null)
						result = result.WithStatement(_syntax.LocalDeclarationStatement(type, variable.Identifier.ValueText));
					else
					{
						var initializerResult = Visit(variable.Initializer.Value);
						var local = _syntax.LocalDeclarationStatement(type, variable.Identifier.ValueText, initializerResult.Expression);
						result = result.WithStatements(initializerResult).WithStatement(local);
					}

					result = result.WithoutExpression();
				}

				return result;
			}

			/// <summary>
			///     Rewrites the <paramref name="statement" />.
			/// </summary>
			public override Result VisitExpressionStatement(ExpressionStatementSyntax statement)
			{
				return Visit(statement.Expression).WithoutExpression();
			}

			/// <summary>
			///     Rewrites the <paramref name="statement" />.
			/// </summary>
			public override Result VisitIfStatement(IfStatementSyntax statement)
			{
				var conditionResult = Visit(statement.Condition);
				var thenResult = Visit(statement.Statement);

				if (statement.Else == null)
				{
					return conditionResult
						.WithStatement(_syntax.IfThenElseStatement(conditionResult.Expression, thenResult.Statements, null))
						.WithoutExpression();
				}

				var elseResult = Visit(statement.Else.Statement);

				return conditionResult
					.WithStatement(_syntax.IfThenElseStatement(conditionResult.Expression, thenResult.Statements, elseResult.Statements))
					.WithoutExpression();
			}

			/// <summary>
			///     Rewrites the <paramref name="block" />.
			/// </summary>
			public override Result VisitBlock(BlockSyntax block)
			{
				var blockResult = block.Statements.Aggregate(Result.Default,
					(result, statement) => result.WithStatements(Visit(statement)).WithoutExpression());

				return Result.Default.WithStatement(SyntaxFactory.Block(blockResult.Statements)).WithoutExpression();
			}

			/// <summary>
			///     Throws an <see cref="InvalidOperationException" />, indicating that <paramref name="node" /> is not supported by the
			///     rewriter.
			/// </summary>
			/// <param name="node">The unsupported syntax node.</param>
			public override Result DefaultVisit(SyntaxNode node)
			{
				Assert.NotReached("Unsupported syntax node: '{0}'.", node.Kind());
				return default(Result);
			}

			/// <summary>
			///     Generates a new variable.
			/// </summary>
			/// <param name="expression">The expression that should be assigned to the variable.</param>
			private GeneratedVariable GenerateVariable(ExpressionSyntax expression)
			{
				Requires.NotNull(expression, () => expression);
				return GenerateVariable(_semanticModel.GetTypeInfo(expression).Type);
			}

			/// <summary>
			///     Generates a new variable.
			/// </summary>
			/// <param name="type">The type of the variable.</param>
			private GeneratedVariable GenerateVariable(ITypeSymbol type)
			{
				Requires.NotNull(type, () => type);

				var variable = new GeneratedVariable(type, _nameScope.MakeUnique("t"));
				_generatedVariables.Add(variable);

				return variable;
			}

			/// <summary>
			///     Represents a local variable generated during the rewrite.
			/// </summary>
			public struct GeneratedVariable
			{
				/// <summary>
				///     Initializes a new instance.
				/// </summary>
				/// <param name="type">The type of the variable.</param>
				/// <param name="name">The name of the variable.</param>
				public GeneratedVariable(ITypeSymbol type, string name)
					: this()
				{
					Requires.NotNull(type, () => type);
					Requires.NotNull(name, () => name);

					Type = type;
					Name = name;
				}

				/// <summary>
				///     Gets the type of the variable.
				/// </summary>
				public ITypeSymbol Type { get; private set; }

				/// <summary>
				///     Gets the name of the variable.
				/// </summary>
				public string Name { get; private set; }

				/// <summary>
				///     Gets the identifier of the variable.
				/// </summary>
				public IdentifierNameSyntax Identifier
				{
					get { return SyntaxFactory.IdentifierName(Name); }
				}
			}

			/// <summary>
			///     Represents the results of a rewrite.
			/// </summary>
			public struct Result
			{
				/// <summary>
				///     Gets the default result.
				/// </summary>
				public static readonly Result Default = new Result((ExpressionSyntax)null);

				/// <summary>
				///     The resulting expression of the rewrite that should be used by subsequent expressions.
				/// </summary>
				private ExpressionSyntax _expression;

				/// <summary>
				///     The sequence of statements that constitute the method's body.
				/// </summary>
				private ImmutableList<StatementSyntax> _statements;

				/// <summary>
				///     Initializes a new instance.
				/// </summary>
				/// <param name="expression">The resulting expression of the rewrite that should be used in subsequent computations.</param>
				public Result(ExpressionSyntax expression)
					: this()
				{
					_expression = expression;
					_statements = ImmutableList<StatementSyntax>.Empty;
				}

				/// <summary>
				///     Initializes a new instance.
				/// </summary>
				/// <param name="statement">The statement that has to be executed.</param>
				public Result(StatementSyntax statement)
					: this()
				{
					_statements = ImmutableList<StatementSyntax>.Empty.Add(statement);
				}

				/// <summary>
				///     Gets the resulting expression of the rewrite that should be used by subsequent expressions.
				/// </summary>
				public ExpressionSyntax Expression
				{
					get
					{
						Requires.That(_expression != null, "No expression has been set.");
						return _expression;
					}
				}

				/// <summary>
				///     Gets the sequence of statements that constitute the method's body.
				/// </summary>
				public IEnumerable<StatementSyntax> Statements
				{
					get { return _statements; }
				}

				/// <summary>
				///     Appends an <see cref="ExpressionStatementSyntax" /> containing the <paramref name="expression" /> to the sequence of
				///     generated <see cref="Statements" />.
				/// </summary>
				/// <param name="expression">The expression that should be appended.</param>
				[Pure]
				public Result WithExpressionStatement(SyntaxNode expression)
				{
					Requires.NotNull(expression, () => expression);
					Requires.OfType<ExpressionSyntax>(expression, () => expression);

					return WithStatement(SyntaxFactory.ExpressionStatement((ExpressionSyntax)expression));
				}

				/// <summary>
				///     Appends the <paramref name="statement" /> to the sequence of generated <see cref="Statements" />.
				/// </summary>
				/// <param name="statement">The statement that should be appended.</param>
				[Pure]
				public Result WithStatement(SyntaxNode statement)
				{
					Requires.NotNull(statement, () => statement);
					Requires.OfType<StatementSyntax>(statement, () => statement);

					return new Result { _expression = _expression, _statements = _statements.Add((StatementSyntax)statement) };
				}

				/// <summary>
				///     Appends the <paramref name="statements" /> to the sequence of generated <see cref="Statements" />.
				/// </summary>
				/// <param name="statements">The statements that should be appended.</param>
				[Pure]
				public Result WithStatements(IEnumerable<StatementSyntax> statements)
				{
					Requires.NotNull(statements, () => statements);
					return new Result { _expression = _expression, _statements = _statements.AddRange(statements) };
				}

				/// <summary>
				///     Appends the <paramref name="result" />'s <see cref="Statements" /> to the sequence of generated
				///     <see cref="Statements" />.
				/// </summary>
				/// <param name="result">The result whose statements should be appended.</param>
				[Pure]
				public Result WithStatements(Result result)
				{
					return WithStatements(result.Statements);
				}

				/// <summary>
				///     Replaces the result's <see cref="Expression" /> with <paramref name="expression" />.
				/// </summary>
				/// <param name="expression">The new resulting expression.</param>
				[Pure]
				public Result WithExpression(ExpressionSyntax expression)
				{
					Requires.NotNull(expression, () => expression);
					return new Result { _expression = expression, _statements = _statements };
				}

				/// <summary>
				///     Replaces the result's <see cref="Expression" /> with the <paramref name="variable" />'s identifier.
				/// </summary>
				/// <param name="variable">The variable representing the result of an expression.</param>
				[Pure]
				public Result WithExpression(GeneratedVariable variable)
				{
					return new Result { _expression = variable.Identifier, _statements = _statements };
				}

				/// <summary>
				///     Removes the result's <see cref="Expression" />.
				/// </summary>
				[Pure]
				public Result WithoutExpression()
				{
					return new Result { _expression = null, _statements = _statements };
				}
			}
		}
	}
}