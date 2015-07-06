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
	using CompilerServices;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;
	using Runtime;

	/// <summary>
	///     Normalizes the initialization of state machines, calling the appropriate builder methods and generating the guard and
	///     action methods.
	/// </summary>
	public sealed class StateMachineNormalizer : SyntaxNormalizer
	{
		/// <summary>
		///     The number of state machine methods that have been generated for the compilation.
		/// </summary>
		private int _stateMachineMethodCount;

		/// <summary>
		///     Normalizes the <paramref name="statement" /> if it is an invocation of a state machine method.
		/// </summary>
		public override SyntaxNode VisitExpressionStatement(ExpressionStatementSyntax statement)
		{
			var invocationExpression = statement.Expression as InvocationExpressionSyntax;
			if (invocationExpression == null)
				return base.VisitExpressionStatement(statement);

			var methodSymbol = invocationExpression.GetReferencedSymbol(SemanticModel);
			if (!methodSymbol.IsStatic)
				return base.VisitExpressionStatement(statement);

			if (methodSymbol.Name != "AddInitialState" && methodSymbol.Name != "AddInitialStates" && methodSymbol.Name != "AddTransition")
				return base.VisitExpressionStatement(statement);

			var isComponentMethod = methodSymbol.ContainingType.Equals(Compilation.GetComponentClassSymbol());
			if (!isComponentMethod)
				return base.VisitExpressionStatement(statement);

			// MetadataBuilders.GetBuilder(this)
			var metadataBuilderSymbol = Syntax.TypeExpression(Compilation.GetTypeSymbol(typeof(MetadataBuilders)));
			var getBuilderMethod = Syntax.MemberAccessExpression(metadataBuilderSymbol, "GetBuilder");
			var builder = Syntax.InvocationExpression(getBuilderMethod, Syntax.ThisExpression());

			if (methodSymbol.Name == "AddTransition")
				return SyntaxFactory.Block(NormalizeTransitions(builder, invocationExpression)).NormalizeWhitespace().EnsureLineCount(statement);

			// .WithInitialStates(states)
			var withInitialStates = Syntax.MemberAccessExpression(builder, "WithInitialStates");
			var arguments = invocationExpression.ArgumentList.Arguments;
			return Syntax.ExpressionStatement(Syntax.InvocationExpression(withInitialStates, arguments)).EnsureLineCount(statement);
		}

		/// <summary>
		///     Normalizes the call to the <see cref="Component.AddTransition{TSource,TTarget}" /> method.
		/// </summary>
		private IEnumerable<StatementSyntax> NormalizeTransitions(SyntaxNode builder, InvocationExpressionSyntax invocationExpression)
		{
			var arguments = invocationExpression.ArgumentList.Arguments;
			var sourceStates = arguments[0].Descendants<MemberAccessExpressionSyntax>();
			var targetStates = arguments[1].Descendants<MemberAccessExpressionSyntax>();

			var guard = Syntax.NullLiteralExpression();
			var action = Syntax.NullLiteralExpression();

			if (arguments.Count > 2)
			{
				if (arguments[2].GetParameterSymbol(SemanticModel).Ordinal == 2)
					guard = GetReflectedMethod(arguments[2].Expression, isGuard: true);
				else
					action = GetReflectedMethod(arguments[2].Expression, isGuard: false);
			}

			if (arguments.Count > 3)
			{
				if (arguments[3].GetParameterSymbol(SemanticModel).Ordinal == 2)
					guard = GetReflectedMethod(arguments[3].Expression, isGuard: true);
				else
					action = GetReflectedMethod(arguments[3].Expression, isGuard: false);
			}

			foreach (var sourceState in sourceStates)
			{
				foreach (var targetState in targetStates)
				{
					// .WithTransition(from, to, guard, action)
					var withTransition = Syntax.MemberAccessExpression(builder, "WithTransition");
					var transitionArguments = new[]
					{
						Syntax.Argument(RefKind.None, sourceState),
						Syntax.Argument(RefKind.None, targetState),
						Syntax.Argument(RefKind.None, guard),
						Syntax.Argument(RefKind.None, action)
					};

					yield return (StatementSyntax)Syntax.ExpressionStatement(Syntax.InvocationExpression(withTransition, transitionArguments));
				}
			}
		}

		/// <summary>
		///     Gets the expression for the reflected method that should be used for the guard or action.
		///     Either generates a method for the specified lambda or or method group.
		/// </summary>
		private ExpressionSyntax GetReflectedMethod(ExpressionSyntax expression, bool isGuard)
		{
			var returnTypeExpression = SyntaxFactory.ParseTypeName(isGuard ? "bool" : "void");
			var methodName = GetMethodName(expression, isGuard);
			var reflectionHelperType = Syntax.TypeExpression(SemanticModel.GetTypeSymbol(typeof(ReflectionHelpers)));
			var getMethod = Syntax.MemberAccessExpression(reflectionHelperType, "GetMethod");

			var declaringType = Syntax.TypeOfExpression(SemanticModel.GetEnclosingSymbol(expression.SpanStart).ContainingType);
			var argumentTypes = Syntax.ArrayCreationExpression<Type>(SemanticModel, Enumerable.Empty<ExpressionSyntax>());

			return (ExpressionSyntax)Syntax.InvocationExpression(getMethod, declaringType,
				Syntax.LiteralExpression(methodName), argumentTypes, SyntaxFactory.TypeOfExpression(returnTypeExpression));
		}

		/// <summary>
		///     Gets the name of the generated method that should be used for the guard or action.
		/// </summary>
		private string GetMethodName(ExpressionSyntax expression, bool isGuard)
		{
			var lambda = expression as ParenthesizedLambdaExpressionSyntax;
			return lambda == null
				? GenerateMethod(Syntax.InvocationExpression(expression), expression.SpanStart, isGuard)
				: GenerateMethod(lambda.Body, expression.SpanStart, isGuard);
		}

		/// <summary>
		///     Generates a method for the <paramref name="methodBody" />.
		/// </summary>
		private string GenerateMethod(SyntaxNode methodBody, int position, bool isGuard)
		{
			var methodName = ((isGuard ? "Guard" : "Action") + _stateMachineMethodCount++).ToSynthesized();

			var method = (MethodDeclarationSyntax)Syntax.MethodDeclaration(
				name: methodName,
				returnType: SyntaxFactory.ParseTypeName(isGuard ? "bool" : "void"),
				accessibility: Accessibility.Private);

			if (methodBody is StatementSyntax)
				method = method.WithBody((BlockSyntax)methodBody);
			else
			{
				method = method.WithBody(null).WithExpressionBody(SyntaxFactory.ArrowExpressionClause((ExpressionSyntax)methodBody));
				method = method.WithSemicolonToken(SyntaxFactory.Token(SyntaxKind.SemicolonToken));
			}

			method = (MethodDeclarationSyntax)Syntax.AddAttributes(method, Syntax.Attribute(typeof(StateMachineMethodAttribute).FullName));

			AddMembers(SemanticModel.GetEnclosingSymbol(position).ContainingType, method);
			return methodName;
		}
	}
}