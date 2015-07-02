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

namespace SafetySharp.Compiler.Normalization.Quotations
{
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Editing;
	using Roslyn.Symbols;
	using Roslyn.Syntax;
	using Runtime;
	using Runtime.Expressions;
	using Runtime.Statements;
	using Utilities;
	using RefKind = Runtime.Expressions.RefKind;

	/// <summary>
	///     Rewrites the body of a method from regular C# code to <see cref="Statement" /> and <see cref="Expression" /> trees.
	/// </summary>
	public sealed class MethodBodyCreationNormalizer : QuotationNormalizer
	{
		/// <summary>
		///     Normalizes the <paramref name="methodDeclaration" />.
		/// </summary>
		protected override SyntaxNode Normalize(MethodDeclarationSyntax methodDeclaration)
		{
			var methodSymbol = methodDeclaration.GetMethodSymbol(SemanticModel);
			var rewriter = new Rewriter(SemanticModel, Syntax);
			var body = rewriter.Rewrite(methodSymbol, methodDeclaration.Body);
			return methodDeclaration.WithBody(body.NormalizeWhitespace());
		}

		/// <summary>
		///     Rewrites a method body.
		/// </summary>
		private class Rewriter : CSharpSyntaxVisitor<SyntaxNode>
		{
			/// <summary>
			///     The semantic model that is used for semantic analysis of the method body.
			/// </summary>
			private readonly SemanticModel _semanticModel;

			/// <summary>
			///     The syntax generator that is used to generate the new method body code.
			/// </summary>
			private readonly SyntaxGenerator _syntax;

			/// <summary>
			///     Initializes a new instance.
			/// </summary>
			/// <param name="semanticModel">The semantic model that should be used for semantic analysis of the method body.</param>
			/// <param name="syntax">The syntax generator that should be used to generate the new method body code.</param>
			public Rewriter(SemanticModel semanticModel, SyntaxGenerator syntax)
			{
				_semanticModel = semanticModel;
				_syntax = syntax;
			}

			/// <summary>
			///     Rewrites the <paramref name="methodBody" /> of the <paramref name="methodSymbol" />.
			/// </summary>
			/// <param name="methodSymbol">The method whose body should be rewritten.</param>
			/// <param name="methodBody">The method body that should be rewritten.</param>
			public BlockSyntax Rewrite(IMethodSymbol methodSymbol, SyntaxNode methodBody)
			{
				var statements = new List<SyntaxNode>();
				var locals = methodBody.Descendants<VariableDeclaratorSyntax>().ToArray();

				// Initialize the metadata for the method's parameters
				foreach (var parameter in methodSymbol.Parameters)
				{
					var type = _syntax.TypeOfExpression(parameter.Type);
					var parameterObject = Create<VariableMetadata>(_syntax.LiteralExpression(parameter.Name), type, _syntax.TrueLiteralExpression());
					statements.Add(_syntax.LocalDeclarationStatement(parameter.Name, parameterObject));
				}

				// new [] { param_1, ..., param_n }
				var parameterNames = methodSymbol.Parameters.Select(p => (ExpressionSyntax)_syntax.IdentifierName(p.Name));
				var parametersArray = _syntax.ArrayCreationExpression<VariableMetadata>(_semanticModel, parameterNames);

				// Initialize the metadata for the method's local variables
				foreach (var local in locals)
				{
					var localSymbol = local.GetDeclaredSymbol<ILocalSymbol>(_semanticModel);
					var type = _syntax.TypeOfExpression(localSymbol.Type);
					var parameterObject = Create<VariableMetadata>(_syntax.LiteralExpression(localSymbol.Name), type, _syntax.FalseLiteralExpression());
					statements.Add(_syntax.LocalDeclarationStatement(localSymbol.Name, parameterObject));
				}

				// new [] { local_1, ..., local_n }
				var localNames = locals.Select(local => (ExpressionSyntax)_syntax.IdentifierName(local.Identifier.ValueText));
				var localsArray = _syntax.ArrayCreationExpression<VariableMetadata>(_semanticModel, localNames);

				// new MethodBody(params, locals, body)
				var body = Visit(methodBody);
				var methodBodyMetadataType = _semanticModel.GetTypeSymbol<MethodBodyMetadata>();
				var methodBodyMetadata = _syntax.ObjectCreationExpression(methodBodyMetadataType, parametersArray, localsArray, body);

				statements.Add(_syntax.ReturnStatement(methodBodyMetadata));
				return SyntaxFactory.Block(statements.Cast<StatementSyntax>());
			}

			/// <summary>
			///     Creates the code that calls <typeparamref name="T" />'s constructor with the <paramref name="arguments" />.
			/// </summary>
			/// <typeparam name="T">The type of the object that should be created.</typeparam>
			/// <param name="arguments">The arguments that should be passed to the constructor.</param>
			private SyntaxNode Create<T>(params SyntaxNode[] arguments)
			{
				return Create<T>((IEnumerable<SyntaxNode>)arguments);
			}

			/// <summary>
			///     Creates the code that calls <typeparamref name="T" />'s constructor with the <paramref name="arguments" />.
			/// </summary>
			/// <typeparam name="T">The type of the object that should be created.</typeparam>
			/// <param name="arguments">The arguments that should be passed to the constructor.</param>
			private SyntaxNode Create<T>(IEnumerable<SyntaxNode> arguments)
			{
				return _syntax.ObjectCreationExpression(_semanticModel.GetTypeSymbol<T>(), arguments);
			}

			/// <summary>
			///     Generates the <see cref="Expression" /> that represents the <paramref name="literal" />.
			/// </summary>
			public override SyntaxNode VisitLiteralExpression(LiteralExpressionSyntax literal)
			{
				var value = _semanticModel.GetConstantValue(literal);
				Assert.That(value.HasValue, "Expected a constant value.");

				if (value.Value is int)
					return Create<IntegerLiteralExpression>(literal);

				if (value.Value is double)
					return Create<DoubleLiteralExpression>(literal);

				if (value.Value is bool)
					return Create<BooleanLiteralExpression>(literal);

				Assert.NotReached("Unsupported literal '{0}'.", literal.ToFullString());
				return null;
			}

			/// <summary>
			///     Generates the <see cref="Expression" /> that represents the <paramref name="identifier" />.
			/// </summary>
			public override SyntaxNode VisitIdentifierName(IdentifierNameSyntax identifier)
			{
				var symbol = identifier.GetReferencedSymbol(_semanticModel);

				switch (symbol.Kind)
				{
					case SymbolKind.Parameter:
					case SymbolKind.Local:
						return Create<VariableExpression>(_syntax.IdentifierName(symbol.Name));
					case SymbolKind.Field:
						var fieldMetadata = ((IFieldSymbol)symbol).GetFieldMetadataExpression(_syntax.ThisExpression(), _syntax);
						return Create<FieldExpression>(fieldMetadata);
					default:
						Assert.NotReached("Unexpected symbol kind '{0}'.", symbol.Kind);
						return null;
				}
			}

			/// <summary>
			///     Generates the <see cref="Expression" /> that represents the <paramref name="assignment" />.
			/// </summary>
			public override SyntaxNode VisitAssignmentExpression(AssignmentExpressionSyntax assignment)
			{
				return Create<AssignmentStatement>(Visit(assignment.Left), Visit(assignment.Right));
			}

			/// <summary>
			///     Generates the <see cref="Expression" /> that represents the <paramref name="expression" />.
			/// </summary>
			public override SyntaxNode VisitParenthesizedExpression(ParenthesizedExpressionSyntax expression)
			{
				return Visit(expression.Expression);
			}

			/// <summary>
			///     Generates the <see cref="Expression" /> that represents the <paramref name="memberAccess" />.
			/// </summary>
			public override SyntaxNode VisitMemberAccessExpression(MemberAccessExpressionSyntax memberAccess)
			{
				var memberSymbol = memberAccess.Name.GetReferencedSymbol(_semanticModel);

				switch (memberSymbol.Kind)
				{
					case SymbolKind.Field:
						if (memberSymbol.ContainingType.TypeKind == TypeKind.Enum)
							return Create<EnumerationLiteralExpression>(memberAccess);

						var fieldMetadata = ((IFieldSymbol)memberSymbol).GetFieldMetadataExpression(memberAccess.Expression, _syntax);
						return Create<FieldExpression>(fieldMetadata);
					default:
						Assert.NotReached("Unsupported member access: {0}.", memberSymbol.Kind);
						return null;
				}
			}

			/// <summary>
			///     Generates the <see cref="Expression" /> that represents the <paramref name="invocation" />.
			/// </summary>
			public override SyntaxNode VisitInvocationExpression(InvocationExpressionSyntax invocation)
			{
				var methodSymbol = invocation.GetReferencedSymbol<IMethodSymbol>(_semanticModel);
				var memberAccess = invocation.Expression as MemberAccessExpressionSyntax;
				var objectExpression = memberAccess == null ? _syntax.ThisExpression() : memberAccess.Expression;
				var methodMetadata = methodSymbol.GetMethodMetadataExpression(objectExpression, _syntax);
				return Create<MethodInvocationExpression>(new[] { methodMetadata }.Concat(invocation.ArgumentList.Arguments.Select(Visit)));
			}

			/// <summary>
			///     Generates the <see cref="Expression" /> that represents the <paramref name="argument" />.
			/// </summary>
			public override SyntaxNode VisitArgument(ArgumentSyntax argument)
			{
				var symbol = argument.GetParameterSymbol(_semanticModel);
				var argumentKindType = _syntax.TypeExpression(_semanticModel.GetTypeSymbol<RefKind>());
				var memberAccess = _syntax.MemberAccessExpression(argumentKindType, symbol.RefKind.ToString());
				return Create<ArgumentExpression>(Visit(argument.Expression), memberAccess);
			}

			/// <summary>
			///     Generates the <see cref="Expression" /> that represents the <paramref name="unaryExpression" />.
			/// </summary>
			public override SyntaxNode VisitPrefixUnaryExpression(PrefixUnaryExpressionSyntax unaryExpression)
			{
				var operand = Visit(unaryExpression.Operand);
				UnaryOperator unaryOperator;

				switch (unaryExpression.Kind())
				{
					case SyntaxKind.UnaryPlusExpression:
						return operand;
					case SyntaxKind.UnaryMinusExpression:
						unaryOperator = UnaryOperator.Minus;
						break;
					case SyntaxKind.LogicalNotExpression:
						unaryOperator = UnaryOperator.Not;
						break;
					default:
						Assert.NotReached("Unsupported unary operator kind.");
						return null;
				}

				var unaryOperatorType = _syntax.TypeExpression(_semanticModel.GetTypeSymbol<UnaryOperator>());
				var memberAccess = _syntax.MemberAccessExpression(unaryOperatorType, _syntax.IdentifierName(unaryOperator.ToString()));
				return Create<UnaryExpression>(memberAccess, operand);
			}

			/// <summary>
			///     Generates the <see cref="Expression" /> that represents the <paramref name="binaryExpression" />.
			/// </summary>
			public override SyntaxNode VisitBinaryExpression(BinaryExpressionSyntax binaryExpression)
			{
				var left = Visit(binaryExpression.Left);
				var right = Visit(binaryExpression.Right);
				var binaryOperator = BinaryOperator.Add;

				switch (binaryExpression.Kind())
				{
					case SyntaxKind.AddExpression:
						binaryOperator = BinaryOperator.Add;
						break;
					case SyntaxKind.SubtractExpression:
						binaryOperator = BinaryOperator.Subtract;
						break;
					case SyntaxKind.MultiplyExpression:
						binaryOperator = BinaryOperator.Multiply;
						break;
					case SyntaxKind.DivideExpression:
						binaryOperator = BinaryOperator.Divide;
						break;
					case SyntaxKind.ModuloExpression:
						binaryOperator = BinaryOperator.Modulo;
						break;
					case SyntaxKind.EqualsExpression:
						binaryOperator = BinaryOperator.Equals;
						break;
					case SyntaxKind.NotEqualsExpression:
						binaryOperator = BinaryOperator.NotEquals;
						break;
					case SyntaxKind.LessThanExpression:
						binaryOperator = BinaryOperator.Less;
						break;
					case SyntaxKind.LessThanOrEqualExpression:
						binaryOperator = BinaryOperator.LessEqual;
						break;
					case SyntaxKind.GreaterThanExpression:
						binaryOperator = BinaryOperator.Greater;
						break;
					case SyntaxKind.GreaterThanOrEqualExpression:
						binaryOperator = BinaryOperator.GreaterEqual;
						break;
					case SyntaxKind.LogicalOrExpression:
					case SyntaxKind.BitwiseOrExpression:
						binaryOperator = BinaryOperator.Or;
						break;
					case SyntaxKind.LogicalAndExpression:
					case SyntaxKind.BitwiseAndExpression:
						binaryOperator = BinaryOperator.And;
						break;
					default:
						Assert.NotReached("Unsupported binary operator kind.");
						break;
				}

				var binaryOperatorType = _syntax.TypeExpression(_semanticModel.GetTypeSymbol<BinaryOperator>());
				var memberAccess = _syntax.MemberAccessExpression(binaryOperatorType, _syntax.IdentifierName(binaryOperator.ToString()));
				return Create<BinaryExpression>(memberAccess, left, right);
			}

			/// <summary>
			///     Generates the <see cref="Expression" /> that represents the <paramref name="conditional" />.
			/// </summary>
			public override SyntaxNode VisitConditionalExpression(ConditionalExpressionSyntax conditional)
			{
				return Create<ConditionalExpression>(Visit(conditional.Condition), Visit(conditional.WhenTrue), Visit(conditional.WhenFalse));
			}

			/// <summary>
			///     Generates the <see cref="Statement" /> that represents the <paramref name="statement" />.
			/// </summary>
			public override SyntaxNode VisitExpressionStatement(ExpressionStatementSyntax statement)
			{
				if (statement.Expression.Kind() == SyntaxKind.SimpleAssignmentExpression)
					return Visit(statement.Expression);

				return Create<ExpressionStatement>(Visit(statement.Expression));
			}

			/// <summary>
			///     Generates the <see cref="Statement" /> that represents the <paramref name="returnStatement" />.
			/// </summary>
			public override SyntaxNode VisitReturnStatement(ReturnStatementSyntax returnStatement)
			{
				if (returnStatement.Expression == null)
					return Create<ReturnStatement>();

				return Create<ReturnStatement>(Visit(returnStatement.Expression));
			}

			/// <summary>
			///     Generates the <see cref="Statement" /> that represents the <paramref name="ifStatement" />.
			/// </summary>
			public override SyntaxNode VisitIfStatement(IfStatementSyntax ifStatement)
			{
				var unaryOperatorType = _syntax.TypeExpression(_semanticModel.GetTypeSymbol<UnaryOperator>());
				var unaryOperator = _syntax.MemberAccessExpression(unaryOperatorType, UnaryOperator.Not.ToString());

				var condition = (ExpressionSyntax)Visit(ifStatement.Condition);
				var thenStatement = (ExpressionSyntax)Visit(ifStatement.Statement);

				if (ifStatement.Else == null)
				{
					var guards = _syntax.ArrayCreationExpression<Expression>(_semanticModel, condition);
					var statements = _syntax.ArrayCreationExpression<Statement>(_semanticModel, thenStatement);
					return Create<ChoiceStatement>(guards, statements, _syntax.TrueLiteralExpression());
				}
				else
				{
					var elseCondition = (ExpressionSyntax)Create<UnaryExpression>(unaryOperator, condition);
					var elseStatement = (ExpressionSyntax)Visit(ifStatement.Else.Statement);

					var guards = _syntax.ArrayCreationExpression<Expression>(_semanticModel, condition, elseCondition);
					var statements = _syntax.ArrayCreationExpression<Statement>(_semanticModel, thenStatement, elseStatement);
					return Create<ChoiceStatement>(guards, statements, _syntax.TrueLiteralExpression());
				}
			}

			/// <summary>
			///     Generates the <see cref="Statement" /> that represents the <paramref name="block" />.
			/// </summary>
			public override SyntaxNode VisitBlock(BlockSyntax block)
			{
				// Unfortunately, we have to take special care for local declarations here; we'll ignore them
				// if they just introduce a new local without assigning a value, otherwise we'll add one (or more)
				// assignment expressions
				var statements = block.Statements.Select(statement =>
				{
					var localDeclaration = statement as LocalDeclarationStatementSyntax;
					if (localDeclaration == null)
						return (IEnumerable<SyntaxNode>)new[] { Visit(statement) };

					var assignments = new List<SyntaxNode>();
					foreach (var declarator in localDeclaration.Declaration.Variables)
					{
						if (declarator.Initializer == null)
							continue;

						var variable = Create<VariableExpression>(_syntax.IdentifierName(declarator.Identifier.ValueText));
						var expression = Visit(declarator.Initializer.Value);
						var assignment = Create<AssignmentStatement>(variable, expression);
						assignments.Add(assignment);
					}

					return assignments;
				}).SelectMany(s => s);

				return Create<BlockStatement>(statements);
			}

			/// <summary>
			///     Throws an <see cref="InvalidOperationException" />, indicating that <paramref name="node" /> is not supported by the
			///     rewriter.
			/// </summary>
			/// <param name="node">The unsupported syntax node.</param>
			public override SyntaxNode DefaultVisit(SyntaxNode node)
			{
				Assert.NotReached("Unsupported syntax node: '{0}'.", node.Kind());
				return null;
			}
		}
	}
}