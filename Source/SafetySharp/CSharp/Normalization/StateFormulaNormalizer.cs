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

namespace SafetySharp.CSharp.Normalization
{
	using System;
	using Extensions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;

	/// <summary>
	///     Rewrites all parameters of method calls with the <see cref="StateFormulaAttribute" />. For instance,
	///     <c>Ltl.Globally(c.Value == 7)</c> is rewritten to <c>Ltl.Globally(Ltl.StateFormula("{0}.Value == 7", c))</c>.
	/// </summary>
	internal class StateFormulaNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     Returns the node unmodified, as the <see cref="StateFormulaAttribute" /> is not supported in constructors.
		/// </summary>
		/// <param name="node">The object creation expression that should be visited.</param>
		public override SyntaxNode VisitObjectCreationExpression(ObjectCreationExpressionSyntax node)
		{
			return node;
		}

		/// <summary>
		///     Rewrites the argument if the underlying method parameter has the <see cref="StateFormulaAttribute" /> applied.
		/// </summary>
		/// <param name="node">The node that should be rewritten.</param>
		public override SyntaxNode VisitArgument(ArgumentSyntax node)
		{
			var requiresRewrite = node.ParameterHasAttribute<StateFormulaAttribute>(SemanticModel);
			node = (ArgumentSyntax)base.VisitArgument(node);

			if (!requiresRewrite)
				return node;

			var className = node.GetMethodSymbol(SemanticModel).ContainingSymbol.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat);
			var expressionString = String.Format("{0}.StateFormula(\"{1}\", {2})", className, node, "null");
			var expression = SyntaxFactory.ParseExpression(expressionString);

			return SyntaxFactory.Argument(expression);
		}

		private void GetAccessedVariables(ArgumentSyntax node)
		{
			
		}
	}
}