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
	using Runtime.Expressions;
	using Runtime.Statements;
	using Utilities;

	/// <summary>
	///     Rewrites the body of a method from regular C# code to <see cref="Statement" /> and <see cref="Expression" /> trees.
	/// </summary>
	public sealed class MethodBodyCreationNormalizer : SyntaxNormalizer
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

			if (methodSymbol.IsAbstract)
				return methodDeclaration;

			_rewriter.Syntax = Syntax;
			_rewriter.SemanticModel = SemanticModel;

			var body = _rewriter.Rewrite(methodSymbol, methodDeclaration.Body);
			return methodDeclaration.WithBody(body.NormalizeWhitespace());
		}

		private class Rewriter : CSharpSyntaxVisitor<SyntaxNode>
		{
			public SemanticModel SemanticModel { get; set; }
			public SyntaxGenerator Syntax { get; set; }

			public BlockSyntax Rewrite(IMethodSymbol methodSymbol, SyntaxNode methodBody)
			{
				var statements = new List<SyntaxNode>();
				var locals = methodBody.Descendants<VariableDeclaratorSyntax>().ToArray();

				foreach (var parameter in methodSymbol.Parameters)
				{
					var type = SyntaxFactory.TypeOfExpression((TypeSyntax)Syntax.TypeExpression(parameter.Type));
					var parameterObject = Create<VariableMetadata>(Syntax.LiteralExpression(parameter.Name), type);
					statements.Add(Syntax.LocalDeclarationStatement(parameter.Name, parameterObject));
				}

				foreach (var local in locals)
				{
					var localSymbol = local.GetDeclaredSymbol<ILocalSymbol>(SemanticModel);
					var type = SyntaxFactory.TypeOfExpression((TypeSyntax)Syntax.TypeExpression(localSymbol.Type));
					var parameterObject = Create<VariableMetadata>(Syntax.LiteralExpression(localSymbol.Name), type);
					statements.Add(Syntax.LocalDeclarationStatement(localSymbol.Name, parameterObject));
				}

				var variableArrayType = Syntax.ArrayTypeExpression(SyntaxFactory.ParseTypeName(typeof(VariableMetadata).FullName));
				var body = Visit(methodBody);

				var localsNames = locals.Select(local => (ExpressionSyntax)Syntax.IdentifierName(local.Identifier.ValueText));
				var localsArguments = SyntaxFactory.SeparatedList(localsNames);
				var localsInitialization = SyntaxFactory.InitializerExpression(SyntaxKind.ArrayInitializerExpression, localsArguments);
				var localsArray = SyntaxFactory.ArrayCreationExpression((ArrayTypeSyntax)variableArrayType, localsInitialization);

				var parametersNames = methodSymbol.Parameters.Select(p => (ExpressionSyntax)Syntax.IdentifierName(p.Name));
				var parametersArguments = SyntaxFactory.SeparatedList(parametersNames);
				var parametersInitialization = SyntaxFactory.InitializerExpression(SyntaxKind.ArrayInitializerExpression, parametersArguments);
				var parametersArray = SyntaxFactory.ArrayCreationExpression((ArrayTypeSyntax)variableArrayType, parametersInitialization);

				var methodBodyMetadataType = SemanticModel.GetTypeSymbol<MethodBodyMetadata>();
				var methodBodyMetadata = Syntax.ObjectCreationExpression(methodBodyMetadataType, parametersArray, localsArray, body);

				statements.Add(Syntax.ReturnStatement(methodBodyMetadata));
				return SyntaxFactory.Block(statements.Cast<StatementSyntax>());
			}

			private SyntaxNode Create<T>(params SyntaxNode[] arguments)
			{
				return Create<T>((IEnumerable<SyntaxNode>)arguments);
			}

			private SyntaxNode Create<T>(IEnumerable<SyntaxNode> arguments)
			{
				return Syntax.ObjectCreationExpression(SemanticModel.GetTypeSymbol<T>(), arguments);
			}

			public override SyntaxNode VisitLiteralExpression(LiteralExpressionSyntax node)
			{
				return Create<IntegerLiteralExpression>(node);
			}

			public override SyntaxNode VisitIdentifierName(IdentifierNameSyntax node)
			{
				var symbol = node.GetReferencedSymbol(SemanticModel);

				switch (symbol.Kind)
				{
					case SymbolKind.Parameter:
					case SymbolKind.Local:
						return Create<VariableExpression>(Syntax.IdentifierName(symbol.Name));
					case SymbolKind.Field:
						var fieldMetadata = ((IFieldSymbol)symbol).GetFieldMetadataExpression(Syntax.ThisExpression(), Syntax);
						return Create<FieldExpression>(fieldMetadata);
					default:
						Assert.NotReached("Unexpected symbol kind.");
						return null;
				}
			}

			public override SyntaxNode VisitAssignmentExpression(AssignmentExpressionSyntax node)
			{
				var symbol = node.Left.GetReferencedSymbol(SemanticModel);

				switch (symbol.Kind)
				{
					case SymbolKind.Parameter:
					case SymbolKind.Local:
						return Create<VariableAssignmentStatement>(Syntax.IdentifierName(symbol.Name), Visit(node.Right));
					case SymbolKind.Field:
						var fieldMetadata = ((IFieldSymbol)symbol).GetFieldMetadataExpression(Syntax.ThisExpression(), Syntax);
						return Create<FieldAssignmentStatement>(fieldMetadata, Visit(node.Right));
					default:
						Assert.NotReached("Unsupported assignment.");
						return null;
				}
			}

			public override SyntaxNode VisitExpressionStatement(ExpressionStatementSyntax node)
			{
				return Visit(node.Expression);
			}

			public override SyntaxNode VisitParenthesizedExpression(ParenthesizedExpressionSyntax node)
			{
				return Visit(node.Expression);
			}

			public override SyntaxNode VisitPrefixUnaryExpression(PrefixUnaryExpressionSyntax node)
			{
				var operand = Visit(node.Operand);
				UnaryOperator unaryOperator;

				switch (node.Kind())
				{
					case SyntaxKind.UnaryPlusExpression:
						return operand;
					case SyntaxKind.UnaryMinusExpression:
						unaryOperator = UnaryOperator.Minus;
						break;
					case SyntaxKind.LogicalNotExpression:
						unaryOperator = UnaryOperator.Not;
						break;
					case SyntaxKind.PreIncrementExpression:
					case SyntaxKind.PreDecrementExpression:
						throw new NotImplementedException();
					default:
						Assert.NotReached("Unsupported unary operator kind.");
						return null;
				}

				var unaryOperatorType = Syntax.TypeExpression(SemanticModel.GetTypeSymbol<UnaryOperator>());
				var memberAccess = Syntax.MemberAccessExpression(unaryOperatorType, Syntax.IdentifierName(unaryOperator.ToString()));
				return Create<UnaryExpression>(memberAccess, operand);
			}

			public override SyntaxNode VisitPostfixUnaryExpression(PostfixUnaryExpressionSyntax node)
			{
				throw new NotImplementedException();
			}

			public override SyntaxNode VisitBinaryExpression(BinaryExpressionSyntax node)
			{
				var left = Visit(node.Left);
				var right = Visit(node.Right);
				var binaryOperator = BinaryOperator.Add;

				switch (node.Kind())
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

				var binaryOperatorType = Syntax.TypeExpression(SemanticModel.GetTypeSymbol<BinaryOperator>());
				var memberAccess = Syntax.MemberAccessExpression(binaryOperatorType, Syntax.IdentifierName(binaryOperator.ToString()));
				return Create<BinaryExpression>(memberAccess, left, right);
			}

			public override SyntaxNode VisitConditionalExpression(ConditionalExpressionSyntax node)
			{
				return Create<ConditionalExpression>(Visit(node.Condition), Visit(node.WhenTrue), Visit(node.WhenFalse));
			}

			public override SyntaxNode VisitReturnStatement(ReturnStatementSyntax node)
			{
				if (node.Expression == null)
					return Create<ReturnStatement>();

				return Create<ReturnStatement>(Visit(node.Expression));
			}

			public override SyntaxNode VisitBlock(BlockSyntax node)
			{
				// Unfortunately, we have to take special care for local declarations here; we'll ignore them
				// if they just introduce a new local without assigning a value, otherwise we'll add one (or more)
				// assignment expressions
				var statements = node.Statements.Select(statement =>
				{
					var localDeclaration = statement as LocalDeclarationStatementSyntax;
					if (localDeclaration == null)
						return (IEnumerable<SyntaxNode>)new[] { Visit(statement) };

					var assignments = new List<SyntaxNode>();
					foreach (var declarator in localDeclaration.Declaration.Variables)
					{
						if (declarator.Initializer == null)
							continue;

						var expression = Visit(declarator.Initializer.Value);
						var assignment = Create<VariableAssignmentStatement>(Syntax.IdentifierName(declarator.Identifier.ValueText), expression);
						assignments.Add(assignment);
					}

					return assignments;
				}).SelectMany(s => s);

				return Create<BlockStatement>(statements);
			}

			public override SyntaxNode DefaultVisit(SyntaxNode node)
			{
				Assert.NotReached("Unsupported syntax node: '{0}'.", node.Kind());
				return null;
			}
		}
	}
}