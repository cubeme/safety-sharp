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
	using System.Globalization;
	using System.Linq;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Roslyn.Syntax;
	using Utilities;

	/// <summary>
	///     Adds omitted optional arguments to all method invocations. The normalizer assumes that optional parameters are of
	///     struct, Boolean, integer, or decimal type.
	/// 
	///     For instance, with method M declared as <c>void M(int a, int b = 2, int c = default(int))</c>:
	///     <code>
	///  		M(1);
	///  		// becomes:
	///  		M(1, b: 2, c : 0);
	///  		
	///  		M(c: 4, a: 1);
	///  		// becomes:
	///  		M(c: 4, a: 1, b: 2);
	/// 	</code>
	/// </summary>
	public class OptionalArgumentNormalizer : BoundTreeNormalizer
	{
		/// <summary>
		///     Adds omitted optional arguments to the <paramref name="invocation" />.
		/// </summary>
		public override SyntaxNode VisitInvocationExpression(InvocationExpressionSyntax invocation)
		{
			// Nothing to do if the method doesn't declare any optional parameters
			var methodSymbol = invocation.GetReferencedSymbol<IMethodSymbol>(SemanticModel);
			if (methodSymbol.Parameters.All(parameter => !parameter.IsOptional))
				return base.VisitInvocationExpression(invocation);

			// Nothing to do if all optional arguments have been provided
			if (invocation.ArgumentList.Arguments.Count == methodSymbol.Parameters.Length)
				return base.VisitInvocationExpression(invocation);

			// Determine the optional parameters that the invocation omits
			var omittedParameters = new HashSet<IParameterSymbol>(methodSymbol.Parameters);
			omittedParameters.ExceptWith(invocation.ArgumentList.Arguments.Select(argument => argument.GetParameterSymbol(SemanticModel)));

			// Recursively normalize the arguments of the invocation
			invocation = (InvocationExpressionSyntax)base.VisitInvocationExpression(invocation);
			var arguments = invocation.ArgumentList.Arguments;

			// Add the default values of all omitted optional arguments as named arguments to the end of the argument list;
			// we can safely ignore param arrays here
			foreach (var omittedParameter in omittedParameters.Where(omittedParameter => !omittedParameter.IsParams))
			{
				Assert.That(omittedParameter.HasExplicitDefaultValue, "Expected an implicit default value.");
				Assert.That(omittedParameter.RefKind == RefKind.None, "Optional parameter cannot be ref or out.");

				// Determine the default value; only structs, decimal, int, and bool are supported
				var defaultValue = String.Empty;
				var value = omittedParameter.ExplicitDefaultValue;
				if (value == null)
					defaultValue = String.Format("default({0})", omittedParameter.Type.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat));
				else if (value is decimal)
					defaultValue = ((decimal)value).ToString(CultureInfo.InvariantCulture) + "m";
				else if (value is int)
					defaultValue = ((int)value).ToString(CultureInfo.InvariantCulture);
				else if (value is bool)
					defaultValue = ((bool)omittedParameter.ExplicitDefaultValue) ? "true" : "false";

				var argument = SyntaxFactory.Argument(SyntaxFactory.NameColon(omittedParameter.Name),
					SyntaxFactory.Token(SyntaxKind.None), SyntaxFactory.ParseExpression(defaultValue));

				arguments = arguments.Add(argument);
			}

			return invocation.WithArgumentList(invocation.ArgumentList.WithArguments(arguments)).NormalizeWhitespace();
		}
	}
}