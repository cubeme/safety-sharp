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

namespace SafetySharp.CSharpCompiler.Roslyn.Syntax
{
	using System;
	using System.Linq;
	using System.Linq.Expressions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling.CompilerServices;
	using Symbols;
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with <see cref="ArgumentSyntax" /> instances.
	/// </summary>
	public static class ArgumentExtensions
	{
		/// <summary>
		///     Gets the <see cref="IMethodSymbol" /> of the method that is called with <paramref name="argument" /> within the context
		///     of the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="argument">The argument the method symbol should be returned for.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve the method symbol.</param>
		[Pure, NotNull]
		public static IMethodSymbol GetMethodSymbol([NotNull] this ArgumentSyntax argument, [NotNull] SemanticModel semanticModel)
		{
			Requires.NotNull(argument, () => argument);
			Requires.NotNull(semanticModel, () => semanticModel);

			var methodCallExpression = argument.GetMethodCallExpression();
			return methodCallExpression.GetReferencedSymbol<IMethodSymbol>(semanticModel);
		}

		/// <summary>
		///     Checks whether the <see cref="IParameterSymbol" /> corresponding to the <paramref name="argument" /> of a
		///     method call is marked with an attribute of type <typeparamref name="T" /> within the context of the
		///     <paramref name="semanticModel" />.
		/// </summary>
		/// <typeparam name="T">
		///     The type of the attribute the method parameter corresponding to the <paramref name="argument" /> should
		///     be marked with.
		/// </typeparam>
		/// <param name="argument">The argument that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve symbols.</param>
		[Pure]
		public static bool HasAttribute<T>([NotNull] this ArgumentSyntax argument, [NotNull] SemanticModel semanticModel)
			where T : Attribute
		{
			Requires.NotNull(argument, () => argument);
			Requires.NotNull(semanticModel, () => semanticModel);

			var parameterSymbol = argument.GetParameterSymbol(semanticModel);
			return parameterSymbol.HasAttribute<T>(semanticModel);
		}

		/// <summary>
		///     Checks whether <paramref name="argument" /> is of type <typeparamref name="T" /> within the context of the
		///     <paramref name="semanticModel" />.
		/// </summary>
		/// <typeparam name="T">The expected type of <paramref name="argument." /></typeparam>
		/// <param name="argument">The argument that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve symbols.</param>
		[Pure]
		public static bool IsOfType<T>([NotNull] this ArgumentSyntax argument, [NotNull] SemanticModel semanticModel)
		{
			Requires.NotNull(argument, () => argument);
			Requires.NotNull(semanticModel, () => semanticModel);

			var typeSymbol = semanticModel.GetTypeSymbol<T>();
			Requires.That(typeSymbol != null, "Unable to determine type symbol of type '{0}'.", typeof(T).FullName);

			return Equals(argument.GetParameterSymbol(semanticModel).Type, typeSymbol);
		}

		/// <summary>
		///     Checks whether <paramref name="argument" /> is of type <paramref name="argumentType" /> within the context of the
		///     <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="argument">The argument that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve symbols.</param>
		/// <param name="argumentType">The expected type of <paramref name="argument." /></param>
		[Pure]
		public static bool IsOfType([NotNull] this ArgumentSyntax argument, [NotNull] SemanticModel semanticModel,
									[NotNull] ITypeSymbol argumentType)
		{
			Requires.NotNull(argument, () => argument);
			Requires.NotNull(semanticModel, () => semanticModel);
			Requires.NotNull(argumentType, () => argumentType);

			return Equals(argument.GetParameterSymbol(semanticModel).Type, argumentType);
		}

		/// <summary>
		///     Checks whether the <paramref name="argument" /> is a Boolean expression argument, i.e., is of type
		///     <c>Expression{Func{bool}}</c> or of type <c>bool</c> with the <see cref="LiftExpressionAttribute" />.
		/// </summary>
		/// <param name="argument">The argument that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve symbols.</param>
		[Pure]
		public static bool IsBooleanExpression([NotNull] this ArgumentSyntax argument, [NotNull] SemanticModel semanticModel)
		{
			Requires.NotNull(argument, () => argument);
			Requires.NotNull(semanticModel, () => semanticModel);

			var funcSymbol = semanticModel.GetTypeSymbol(typeof(Func<>)).Construct(semanticModel.GetTypeSymbol<bool>());
			var expressionSymbol = semanticModel.GetTypeSymbol(typeof(Expression<>)).Construct(funcSymbol);
			var isExpression = argument.IsOfType(semanticModel, expressionSymbol);
			var isLiftedBoolean = argument.IsOfType<bool>(semanticModel) && argument.HasAttribute<LiftExpressionAttribute>(semanticModel);
			return isLiftedBoolean || isExpression;
		}

		/// <summary>
		///     Gets the <see cref="InvocationExpressionSyntax" /> or the <see cref="ObjectCreationExpressionSyntax" />
		///     that contains the <paramref name="argument" />.
		/// </summary>
		/// <param name="argument">The argument the method call expression should be returned for.</param>
		[Pure, NotNull]
		public static ExpressionSyntax GetMethodCallExpression([NotNull] this ArgumentSyntax argument)
		{
			Requires.NotNull(argument, () => argument);

			for (var node = argument.Parent; node != null; node = node.Parent)
			{
				if (node is InvocationExpressionSyntax || node is ObjectCreationExpressionSyntax)
					return node as ExpressionSyntax;
			}

			Assert.NotReached("Unable to find the method call expression containing argument '{0}'.", argument);
			return null;
		}

		/// <summary>
		///     Gets the <see cref="IParameterSymbol" /> corresponding to <paramref name="argument" /> within the context of the
		///     <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="argument">The argument the parameter symbol should be returned for.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve symbols.</param>
		/// <remarks>
		///     There might be an official Roslyn API one day that should be used to replace this method
		///     (see also https://roslyn.codeplex.com/discussions/541303).
		/// </remarks>
		[Pure, NotNull]
		public static IParameterSymbol GetParameterSymbol([NotNull] this ArgumentSyntax argument, [NotNull] SemanticModel semanticModel)
		{
			Requires.NotNull(argument, () => argument);
			Requires.NotNull(semanticModel, () => semanticModel);

			var methodCallExpression = argument.GetMethodCallExpression();
			var methodSymbol = methodCallExpression.GetReferencedSymbol<IMethodSymbol>(semanticModel);

			// If this is a named argument, simply look up the parameter symbol by name.
			if (argument.NameColon != null)
				return methodSymbol.Parameters.Single(parameter => parameter.Name == argument.NameColon.Name.Identifier.ValueText);

			// Otherwise, get the corresponding invocation or object creation expression and match the argument.
			SeparatedSyntaxList<ArgumentSyntax> arguments;
			var invocationExpression = methodCallExpression as InvocationExpressionSyntax;
			var objectCreationExpression = methodCallExpression as ObjectCreationExpressionSyntax;

			if (invocationExpression != null)
				arguments = invocationExpression.ArgumentList.Arguments;
			else
				arguments = objectCreationExpression.ArgumentList.Arguments;

			for (var i = 0; i < arguments.Count; ++i)
			{
				// If this is a method with a params parameter at the end, we might have more arguments than parameters. In that case,
				// return the parameter symbol for the params parameter if the argument exceeds the parameter count.
				if (i >= methodSymbol.Parameters.Length)
				{
					var lastParameter = methodSymbol.Parameters[methodSymbol.Parameters.Length - 1];
					if (lastParameter.IsParams)
						return lastParameter;

					Assert.NotReached("There are more arguments than parameters.");
				}

				if (arguments[i] == argument)
					return methodSymbol.Parameters[i];
			}

			Assert.NotReached("Unable to determine parameter symbol for argument '{0}'.", argument);
			return null;
		}
	}
}