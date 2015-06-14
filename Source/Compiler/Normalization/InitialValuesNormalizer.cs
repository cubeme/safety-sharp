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
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;
	using Runtime;

	/// <summary>
	///     Replaces all invocations of <see cref="Component.SetInitialValues{T}(T,T[])" /> with
	///     <see cref="ComponentInfo.Builder.WithInitialValues" />.
	/// </summary>
	public sealed class InitialValuesNormalizer : SyntaxNormalizer
	{
		/// <summary>
		///     Normalizes the <paramref name="statement" /> if it is an invocation of
		///     <see cref="Component.SetInitialValues{T}(T,T[])" />.
		/// </summary>
		public override SyntaxNode VisitExpressionStatement(ExpressionStatementSyntax statement)
		{
			var invocationExpression = statement.Expression as InvocationExpressionSyntax;
			if (invocationExpression == null)
				return base.VisitExpressionStatement(statement);

			var methodSymbol = invocationExpression.GetReferencedSymbol(SemanticModel);
			if (!methodSymbol.ContainingType.Equals(Compilation.GetComponentClassSymbol()) || methodSymbol.Name != "SetInitialValues")
				return statement;

			// MetadataBuilders.GetBuilder(this)
			var metadataBuilderSymbol = Syntax.TypeExpression(Compilation.GetTypeSymbol(typeof(MetadataBuilders)));
			var getBuilderMethod = Syntax.MemberAccessExpression(metadataBuilderSymbol, "GetBuilder");
			var builder = Syntax.InvocationExpression(getBuilderMethod, Syntax.ThisExpression());

			// ReflectionHelpers.GetField(typeof(...), typeof(...), "...")
			var symbol = invocationExpression.ArgumentList.Arguments[0].Expression.GetReferencedSymbol(SemanticModel);
			var fieldSymbol = symbol as IFieldSymbol;
			if (fieldSymbol == null)
				return statement; // TODO: Remove once the expression overload of SetInitialValues is removed

			var fieldInfo = fieldSymbol.GetRuntimeFieldExpression(Syntax);

			// .WithInitialValues()
			var withInitialValues = Syntax.MemberAccessExpression(builder, "WithInitialValues");
			var arguments = new List<ArgumentSyntax>(invocationExpression.ArgumentList.Arguments.Skip(1));
			arguments.Insert(0, (ArgumentSyntax)Syntax.Argument(fieldInfo));
			return Syntax.ExpressionStatement(Syntax.InvocationExpression(withInitialValues, arguments)).EnsureLineCount(statement);
		}
	}
}