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

namespace SafetySharp.CSharp.Extensions
{
	using System;
	using System.Linq;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with <see cref="ArgumentSyntax" /> instances.
	/// </summary>
	internal static class ArgumentExtensions
	{
		/// <summary>
		///     Gets the <see cref="IMethodSymbol" /> of the <see cref="InvocationExpressionSyntax" /> that contains
		///     <paramref name="argument" />.
		/// </summary>
		/// <param name="argument">The argument the <see cref="InvocationExpressionSyntax" /> should be returned for.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve the symbol.</param>
		internal static IMethodSymbol GetMethodSymbol(this ArgumentSyntax argument, SemanticModel semanticModel)
		{
			Argument.NotNull(argument, () => argument);
			Argument.NotNull(semanticModel, () => semanticModel);

			var invocationExpression = argument.GetInvocationExpression();
			var methodSymbol = semanticModel.GetSymbolInfo(invocationExpression).Symbol as IMethodSymbol;
			Assert.NotNull(methodSymbol, "Unable to determine symbol of invocation '{0}'.", invocationExpression);

			return methodSymbol;
		}

		/// <summary>
		///     Checks whether the <see cref="IParameterSymbol" /> corresponding to the <paramref name="argument" /> of an
		///     <see cref="InvocationExpressionSyntax" /> has the attribute of type <typeparamref name="T" /> applied.
		/// </summary>
		/// <param name="argument">The argument that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be used for symbol resolution.</param>
		internal static bool ParameterHasAttribute<T>(this ArgumentSyntax argument, SemanticModel semanticModel)
		{
			Argument.NotNull(argument, () => argument);
			Argument.NotNull(semanticModel, () => semanticModel);

			var attributeSymbol = semanticModel.GetTypeSymbol<T>();
			return argument.GetParameterSymbol(semanticModel).GetAttributes().Any(attribute => attribute.AttributeClass.Equals(attributeSymbol));
		}

		/// <summary>
		///     Gets the <see cref="InvocationExpressionSyntax" /> that contains <paramref name="argument" />.
		/// </summary>
		/// <param name="argument">The argument the <see cref="InvocationExpressionSyntax" /> should be returned for.</param>
		private static InvocationExpressionSyntax GetInvocationExpression(this ArgumentSyntax argument)
		{
			Argument.NotNull(argument, () => argument);

			var parent = argument.Parent;
			while (!(parent is InvocationExpressionSyntax))
			{
				Assert.That(!(parent is ObjectCreationExpressionSyntax), "The argument is part of an object creation expression.");
				parent = parent.Parent;
			}

			Assert.NotNull(parent, "Unable to find the invocation expression containing argument '{0}'.", argument);
			return parent as InvocationExpressionSyntax;
		}

		/// <summary>
		///     Gets the <see cref="IParameterSymbol" /> corresponding to <paramref name="argument" />.
		///     TODO: There might be an official Roslyn API one day that should be used to replace this method.
		///     (see also https://roslyn.codeplex.com/discussions/541303)
		/// </summary>
		/// <param name="argument">The <see cref="ArgumentSyntax" /> node the <see cref="IParameterSymbol" /> should be returned for.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve the symbol.</param>
		private static IParameterSymbol GetParameterSymbol(this ArgumentSyntax argument, SemanticModel semanticModel)
		{
			Argument.NotNull(argument, () => argument);
			Argument.NotNull(semanticModel, () => semanticModel);

			var invocationExpression = argument.GetInvocationExpression();
			var methodSymbol = argument.GetMethodSymbol(semanticModel);

			if (argument.NameColon != null)
				return methodSymbol.Parameters.Single(parameter => parameter.Name == argument.NameColon.Name.Identifier.ValueText);

			for (var i = 0; i < invocationExpression.ArgumentList.Arguments.Count; ++i)
			{
				if (i >= methodSymbol.Parameters.Length)
				{
					var lastParameter = methodSymbol.Parameters[methodSymbol.Parameters.Count() - 1];
					if (lastParameter.IsParams)
						return lastParameter;

					Assert.NotReached("There are more arguments than parameters.");
				}

				if (invocationExpression.ArgumentList.Arguments[i].Equals(argument))
					return methodSymbol.Parameters[i];
			}

			Assert.NotReached("Unable to determine parameter symbol for argument '{0}'.", argument);
			return null;
		}
	}
}