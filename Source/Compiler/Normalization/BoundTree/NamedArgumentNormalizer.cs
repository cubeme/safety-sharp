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
	using System.Linq;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Roslyn.Syntax;

	/// <summary>
	///     Reorders the arguments of all method invocations using named arguments such that the order of the arguments match the
	///     order of the pararmeters of the method declaration. Additionally, the argument names are removed from the invocation.
	///     It is assumed that the invocations do not omit any optional parameters.
	/// 
	///     For instance, with method M declared as <c>void M(int a, int b)</c>:
	///     <code>
	///   		M(b: 1, a: 2);
	///   		// becomes:
	///   		M(2, 1);
	///   		
	///   		M(1, b: 2);
	///   		// becomes:
	///   		M(1, 2);
	///  	</code>
	/// </summary>
	public class NamedArgumentNormalizer : BoundTreeNormalizer
	{
		/// <summary>
		///     Reorders the named arguments of the <paramref name="invocation" />.
		/// </summary>
		public override SyntaxNode VisitInvocationExpression(InvocationExpressionSyntax invocation)
		{
			// Nothing to do if no named arguments are used
			if (invocation.ArgumentList.Arguments.All(argument => argument.NameColon == null))
				return base.VisitInvocationExpression(invocation);

			// Determine the correct order of the arguments, recursively normalize the arguments and remove the argument name
			var orderedArguments =
				from argument in invocation.ArgumentList.Arguments
				let parameterSymbol = argument.GetParameterSymbol(SemanticModel)
				orderby parameterSymbol.Ordinal
				select ((ArgumentSyntax)VisitArgument(argument)).WithNameColon(null);

			var argumentList = SyntaxFactory.ArgumentList(SyntaxFactory.SeparatedList(orderedArguments));
			return invocation.WithArgumentList(argumentList).NormalizeWhitespace();
		}
	}
}