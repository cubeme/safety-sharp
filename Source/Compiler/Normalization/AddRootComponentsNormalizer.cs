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
	using CompilerServices;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;
	using Runtime;

	/// <summary>
	///     Replaces all invocations of the <see cref="Model.AddRootComponent" /> and
	///     <see cref="Model.AddRootComponents" /> methods with an invocation of
	///     <see cref="ModelMetadata.Builder.WithRootComponents" />
	/// </summary>
	public sealed class AddRootComponentsNormalizer : SyntaxNormalizer
	{
		/// <summary>
		///     Normalizes the <paramref name="statement" /> if it is an invocation of
		///     <see cref="Model.AddRootComponent" /> or <see cref="Model.AddRootComponents" />.
		/// </summary>
		public override SyntaxNode VisitExpressionStatement(ExpressionStatementSyntax statement)
		{
			var invocationExpression = statement.Expression as InvocationExpressionSyntax;
			if (invocationExpression == null)
				return base.VisitExpressionStatement(statement);

			var methodSymbol = invocationExpression.GetReferencedSymbol(SemanticModel);
			if (methodSymbol.Name != "AddRootComponent" && methodSymbol.Name != "AddRootComponents")
				return base.VisitExpressionStatement(statement);

			if (!methodSymbol.ContainingType.Equals(Compilation.GetModelClassSymbol()))
				return base.VisitExpressionStatement(statement);

			// MetadataBuilders.GetBuilder(target)
			var metadataBuilderType = Syntax.TypeExpression(SemanticModel.GetTypeSymbol(typeof(MetadataBuilders)));
			var getBuilderMethod = Syntax.MemberAccessExpression(metadataBuilderType, "GetBuilder");
			var invokedMemberExpression = invocationExpression.Expression as MemberAccessExpressionSyntax;
			var builderTarget = invokedMemberExpression == null ? Syntax.ThisExpression() : invokedMemberExpression.Expression.RemoveTrivia();
			var getBuilder = Syntax.InvocationExpression(getBuilderMethod, builderTarget);

			// .WithRootComponents(components)
			var withRootComponents = Syntax.MemberAccessExpression(getBuilder, "WithRootComponents");
			var arguments = invocationExpression.Descendants<ArgumentSyntax>();
			return Syntax.ExpressionStatement(Syntax.InvocationExpression(withRootComponents, arguments)).EnsureLineCount(statement);
		}
	}
}