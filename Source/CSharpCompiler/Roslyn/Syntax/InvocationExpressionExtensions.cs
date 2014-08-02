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
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;
	using Symbols;
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with <see cref="InvocationExpressionSyntax" /> instances.
	/// </summary>
	public static class InvocationExpressionExtensions
	{
		/// <summary>
		///     Checks whether the <paramref name="invocationExpression" /> invokes a CTL or LTL formula function within the context of
		///     the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="invocationExpression">The invocation expression that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve symbols.</param>
		public static bool IsFormulaFunctionInvocation(this InvocationExpressionSyntax invocationExpression, SemanticModel semanticModel)
		{
			Requires.NotNull(invocationExpression, () => invocationExpression);
			Requires.NotNull(semanticModel, () => semanticModel);

			var methodSymbol = invocationExpression.GetReferencedSymbol<IMethodSymbol>(semanticModel);
			var methodClass = methodSymbol.ContainingType;

			return methodClass == semanticModel.GetTypeSymbol(typeof(Ltl)) ||
				   methodClass == semanticModel.GetTypeSymbol(typeof(Ctl)) ||
				   methodClass == semanticModel.GetTypeSymbol(typeof(CtlOperatorFactory)) ||
				   methodClass == semanticModel.GetTypeSymbol(typeof(LtlFormula)) ||
				   methodClass == semanticModel.GetTypeSymbol(typeof(CtlFormula));
		}
	}
}