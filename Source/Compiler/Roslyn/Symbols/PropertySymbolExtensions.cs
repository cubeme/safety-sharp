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

namespace SafetySharp.Compiler.Roslyn.Symbols
{
	using System;
	using System.Linq;
	using CompilerServices;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Editing;
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with <see cref="IPropertySymbol" /> instances.
	/// </summary>
	public static class PropertySymbolExtensions
	{
		/// <summary>
		///     Checks whether <paramref name="propertySymbol" /> overrides <paramref name="overriddenProperty" />.
		/// </summary>
		/// <param name="propertySymbol">The symbol of the property that should be checked.</param>
		/// <param name="overriddenProperty">The symbol of the property that should be overridden.</param>
		[Pure]
		public static bool Overrides([NotNull] this IPropertySymbol propertySymbol, [NotNull] IPropertySymbol overriddenProperty)
		{
			Requires.NotNull(propertySymbol, () => propertySymbol);
			Requires.NotNull(overriddenProperty, () => overriddenProperty);

			if (propertySymbol.Equals(overriddenProperty))
				return true;

			if (!propertySymbol.IsOverride)
				return false;

			if (propertySymbol.OverriddenProperty.Equals(overriddenProperty))
				return true;

			return propertySymbol.OverriddenProperty.Overrides(overriddenProperty);
		}

		/// <summary>
		///     Gets a value indicating whether <paramref name="propertySymbol" /> is defined as an auto-implemented property.
		/// </summary>
		/// <param name="propertySymbol">The symbol of the property that should be checked.</param>
		[Pure]
		public static bool IsAutoProperty([NotNull] this IPropertySymbol propertySymbol)
		{
			Requires.NotNull(propertySymbol, () => propertySymbol);

			if (propertySymbol.DeclaringSyntaxReferences.Length != 1)
				return false;

			var declaration = (PropertyDeclarationSyntax)propertySymbol.DeclaringSyntaxReferences[0].GetSyntax();
			var getter = declaration.AccessorList.Accessors.SingleOrDefault(accessor => accessor.Kind() == SyntaxKind.GetAccessorDeclaration);

			if (getter == null)
				return false;

			return getter.Body == null;
		}

		/// <summary>
		///     Gets the expression that selects the <paramref name="propertySymbol" /> at runtime using reflection.
		/// </summary>
		/// <param name="propertySymbol">The property the code should be generated for.</param>
		/// <param name="syntaxGenerator">The syntax generator that should be used.</param>
		[Pure]
		public static ExpressionSyntax GetPropertyInfoExpression([NotNull] this IPropertySymbol propertySymbol,
																 [NotNull] SyntaxGenerator syntaxGenerator)
		{
			Requires.NotNull(propertySymbol, () => propertySymbol);
			Requires.NotNull(syntaxGenerator, () => syntaxGenerator);

			var declaringTypeArg = SyntaxFactory.TypeOfExpression((TypeSyntax)syntaxGenerator.TypeExpression(propertySymbol.ContainingType));
			var propertyTypeArg = SyntaxFactory.TypeOfExpression((TypeSyntax)syntaxGenerator.TypeExpression(propertySymbol.Type));
			var nameArg = syntaxGenerator.LiteralExpression(propertySymbol.Name);
			var reflectionHelpersType = SyntaxFactory.ParseTypeName(typeof(ReflectionHelpers).FullName);
			var getFieldMethod = syntaxGenerator.MemberAccessExpression(reflectionHelpersType, "GetProperty");
			return (ExpressionSyntax)syntaxGenerator.InvocationExpression(getFieldMethod, declaringTypeArg, propertyTypeArg, nameArg);
		}
	}
}