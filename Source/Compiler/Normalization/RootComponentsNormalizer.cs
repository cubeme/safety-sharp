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
	///     Replaces all invocations of the <see cref="Model.AddRootComponent" /> and
	///     <see cref="Model.AddRootComponents" /> methods with an invocation of
	///     <see cref="ModelMetadata.Builder.WithRootComponents" />
	/// </summary>
	public sealed class RootComponentsNormalizer : SyntaxNormalizer
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
			var invokedMemberExpression = invocationExpression.Expression as MemberAccessExpressionSyntax;
			var builderTarget = invokedMemberExpression == null ? Syntax.ThisExpression() : invokedMemberExpression.Expression.RemoveTrivia();
			var getBuilder = GetBuilder(builderTarget);

			// .WithRootComponents(components)
			var withRootComponents = Syntax.MemberAccessExpression(getBuilder, "WithRootComponents");
			var componentArguments = invocationExpression.ArgumentList.Arguments;
			var withRootsInvocation = Syntax.ExpressionStatement(Syntax.InvocationExpression(withRootComponents, componentArguments));

			// MetadataBuilders.GetBuilder(component).WithName(nameof(arg), compilerGenerated: true)
			var argumentStatements = GetNameStatements(componentArguments);

			var statements = new[] { (ExpressionStatementSyntax)withRootsInvocation }.Concat(argumentStatements);
			var block = SyntaxFactory.Block(statements);
			return block.NormalizeWhitespace().EnsureLineCount(statement);
		}

		/// <summary>
		///     Gets the component name assignment statements for the <paramref name="arguments" />.
		/// </summary>
		/// <param name="arguments">The arguments that should be analyzed to see if a component name can be generated.</param>
		private IEnumerable<ExpressionStatementSyntax> GetNameStatements(IEnumerable<ArgumentSyntax> arguments)
		{
			foreach (var argument in arguments)
			{
				var symbol = SemanticModel.GetSymbolInfo(argument.Expression).Symbol;

				var fieldSymbol = symbol as IFieldSymbol;
				var propertySymbol = symbol as IPropertySymbol;
				var localSymbol = symbol as ILocalSymbol;
				var parameterSymbol = symbol as IParameterSymbol;

				if (fieldSymbol == null && propertySymbol == null && localSymbol == null && parameterSymbol == null)
					continue;

				if (propertySymbol != null && !propertySymbol.IsAutoProperty())
					continue;

				var getBuilder = GetBuilder(argument.Expression);
				var name = "<>";
				
				if (fieldSymbol != null)
					name = fieldSymbol.Name;

				if (propertySymbol != null)
					name = propertySymbol.Name;

				if (localSymbol != null)
					name = localSymbol.Name;

				if (parameterSymbol != null)
					name = parameterSymbol.Name;

				// WithName(name, true)
				var withName = Syntax.MemberAccessExpression(getBuilder, "WithName");
				var invocation = Syntax.InvocationExpression(withName, Syntax.LiteralExpression(name), Syntax.TrueLiteralExpression());
				yield return (ExpressionStatementSyntax)Syntax.ExpressionStatement(invocation);
			}
		}

		/// <summary>
		///     Gets the expression that retrieves the builder for the object represented by <paramref name="targetExpression" />.
		/// </summary>
		/// <param name="targetExpression">The expression the builder should be retrieved for.</param>
		private SyntaxNode GetBuilder(SyntaxNode targetExpression)
		{
			var metadataBuilderType = Syntax.TypeExpression(SemanticModel.GetTypeSymbol(typeof(MetadataBuilders)));
			var getBuilderMethod = Syntax.MemberAccessExpression(metadataBuilderType, "GetBuilder");
			return Syntax.InvocationExpression(getBuilderMethod, targetExpression);
		}
	}
}