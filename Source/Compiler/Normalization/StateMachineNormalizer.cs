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
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;
	using Runtime;
	using Utilities;

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
			{
				// .WithTransition(from, to, guard, action)
				var withTransition = Syntax.MemberAccessExpression(builder, "WithTransition");
				var transitionArguments = GetTransitionArguments(invocationExpression);
				return Syntax.ExpressionStatement(Syntax.InvocationExpression(withTransition, transitionArguments)).EnsureLineCount(statement);
			}

			// .WithInitialStates(states)
			var withInitialStates = Syntax.MemberAccessExpression(builder, "WithInitialStates");
			var arguments = invocationExpression.ArgumentList.Arguments;
			return Syntax.ExpressionStatement(Syntax.InvocationExpression(withInitialStates, arguments)).EnsureLineCount(statement);
		}

		/// <summary>
		///     Gets the arguments for the <see cref="ComponentMetadata.Builder.WithTransition" /> method.
		/// </summary>
		private IEnumerable<ArgumentSyntax> GetTransitionArguments(InvocationExpressionSyntax invocationExpression)
		{
			var arguments = from argument in invocationExpression.ArgumentList.Arguments
							let parameter = argument.GetParameterSymbol(SemanticModel)
							orderby parameter.Ordinal
							select new { argument.Expression, Parameter = parameter };

			var index = 0;
			foreach (var argument in arguments)
			{
				var expression = argument.Expression;

				for (; index < argument.Parameter.Ordinal; ++index)
					yield return (ArgumentSyntax)Syntax.Argument(RefKind.None, Syntax.NullLiteralExpression());

				if (argument.Parameter.Ordinal == 2 || argument.Parameter.Ordinal == 3)
				{
					var returnType = argument.Parameter.Ordinal == 2 ? "bool" : "void";
					var returnTypeExpression = SyntaxFactory.ParseTypeName(returnType);
					var methodName = GetMethodName(expression, returnTypeExpression);
					var reflectionHelperType = Syntax.TypeExpression(SemanticModel.GetTypeSymbol(typeof(ReflectionHelpers)));
					var getMethod = Syntax.MemberAccessExpression(reflectionHelperType, "GetMethod");

					var declaringType = Syntax.TypeOfExpression(SemanticModel.GetEnclosingSymbol(invocationExpression.SpanStart).ContainingType);
					var argumentTypes = Syntax.ArrayCreationExpression<Type>(SemanticModel, Enumerable.Empty<ExpressionSyntax>());

					expression = (ExpressionSyntax)Syntax.InvocationExpression(getMethod, declaringType, 
						Syntax.LiteralExpression(methodName), argumentTypes, SyntaxFactory.TypeOfExpression(returnTypeExpression));
				}

				++index;
				yield return (ArgumentSyntax)Syntax.Argument(RefKind.None, expression).NormalizeWhitespace();
			}

			for (; index < 4; ++index)
				yield return (ArgumentSyntax)Syntax.Argument(RefKind.None, Syntax.NullLiteralExpression());
		}

		/// <summary>
		///     Gets the name of the method that should be used for the guard or action. Either generates a method for a lambda or uses
		///     the name of the non-anonymous method.
		/// </summary>
		private string GetMethodName(ExpressionSyntax expression, SyntaxNode returnType)
		{
			var lambda = expression as ParenthesizedLambdaExpressionSyntax;
			if (lambda != null)
				return GenerateMethod(lambda, returnType);

			var identifier = expression as IdentifierNameSyntax;
			if (identifier != null)
				return identifier.Identifier.ValueText;

			Assert.NotReached("Unexpected guard or action expression: '{0}'.", expression.Kind());
			return null;
		}

		/// <summary>
		///     Generates a method for the <paramref name="lambda" />.
		/// </summary>
		private string GenerateMethod(ParenthesizedLambdaExpressionSyntax lambda, SyntaxNode returnType)
		{
			var methodName = ("StateMachineMethod" + _stateMachineMethodCount++).ToSynthesized();
			var body = lambda.Body is ExpressionSyntax ? Syntax.ReturnStatement(lambda.Body) : lambda.Body;

			var method = Syntax.MethodDeclaration(
				name: methodName,
				returnType: returnType,
				statements: new[] { body },
				accessibility: Accessibility.Private);

			AddMembers(SemanticModel.GetEnclosingSymbol(lambda.SpanStart).ContainingType, (MemberDeclarationSyntax)method);
			return methodName;
		}
	}
}