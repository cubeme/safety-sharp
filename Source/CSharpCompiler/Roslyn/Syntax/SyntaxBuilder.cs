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
	using System.Collections.Generic;
	using System.Linq;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Utilities;

	/// <summary>
	///     Provides helper methods for creating C# syntax nodes.
	/// </summary>
	public static class SyntaxBuilder
	{
		/// <summary>
		///     Creates a <see cref="SyntaxTokenList" /> containing the appropriate modifier(s) for the desired
		///     <paramref name="visibility" />.
		/// </summary>
		/// <param name="visibility">The visibility the <see cref="SyntaxTokenList" /> should be created for.</param>
		private static SyntaxTokenList VisibilityModifier(Visibility visibility)
		{
			switch (visibility)
			{
				case Visibility.Private:
					return SyntaxFactory.TokenList(SyntaxFactory.Token(SyntaxKind.PrivateKeyword));
				case Visibility.Protected:
					return SyntaxFactory.TokenList(SyntaxFactory.Token(SyntaxKind.ProtectedKeyword));
				case Visibility.ProtectedInternal:
					var @protected = SyntaxFactory.Token(SyntaxKind.ProtectedKeyword).WithTrailingTrivia(SyntaxFactory.Space);
					var @internal = SyntaxFactory.Token(SyntaxKind.InternalKeyword);
					return SyntaxFactory.TokenList(@protected, @internal);
				case Visibility.Internal:
					return SyntaxFactory.TokenList(SyntaxFactory.Token(SyntaxKind.InternalKeyword));
				case Visibility.Public:
					return SyntaxFactory.TokenList(SyntaxFactory.Token(SyntaxKind.PublicKeyword));
				default:
					throw new ArgumentOutOfRangeException("visibility");
			}
		}

		/// <summary>
		///     Creates an <see cref="AccessorDeclarationSyntax" /> with the given <paramref name="accessorType" /> and
		///     <paramref name="visibility" />.
		/// </summary>
		/// <param name="accessorType">The type of the accessor.</param>
		/// <param name="visibility">
		///     The visibility of the accessor. A value of <c>null</c> indicates that no visibility modifier should
		///     be added to the accessor.
		/// </param>
		private static AccessorDeclarationSyntax Accessor(SyntaxKind accessorType, Visibility? visibility)
		{
			Requires.InRange(accessorType, () => accessorType);

			var accessor = SyntaxFactory.AccessorDeclaration(accessorType).WithSemicolonToken(SyntaxFactory.Token(SyntaxKind.SemicolonToken));

			if (!visibility.HasValue)
				return accessor;

			return accessor.WithLeadingSpace().WithModifiers(VisibilityModifier(visibility.Value));
		}

		/// <summary>
		///     Creates a <see cref="PropertyDeclarationSyntax" /> for an auto-implemented property with both a getter and a setter.
		/// </summary>
		/// <param name="propertyName">The name of the property.</param>
		/// <param name="propertyType">The type of the property.</param>
		/// <param name="visibility">The visibility of the property.</param>
		/// <param name="getterVisibility">
		///     The visibility of the property's getter. A value of <c>null</c> indicates that no visibility
		///     modifier should be added to the getter.
		/// </param>
		/// <param name="setterVisibility">
		///     The visibility of the property's setter. A value of <c>null</c> indicates that no visibility
		///     modifier should be added to the setter.
		/// </param>
		public static PropertyDeclarationSyntax AutoProperty(string propertyName, string propertyType, Visibility visibility,
															 Visibility? getterVisibility, Visibility? setterVisibility)
		{
			Requires.NotNullOrWhitespace(propertyName, () => propertyName);
			Requires.NotNullOrWhitespace(propertyType, () => propertyType);
			Requires.That(!getterVisibility.HasValue || !setterVisibility.HasValue, "Cannot specify visibility modifiers for both accessors.");

			var type = SyntaxFactory.ParseTypeName(propertyType).WithLeadingAndTrailingSpace();
			var property = SyntaxFactory.PropertyDeclaration(type, propertyName).WithModifiers(VisibilityModifier(visibility));
			var getter = Accessor(SyntaxKind.GetAccessorDeclaration, getterVisibility).WithLeadingSpace();
			var setter = Accessor(SyntaxKind.SetAccessorDeclaration, setterVisibility).WithLeadingAndTrailingSpace();
			var accessors = SyntaxFactory.AccessorList(SyntaxFactory.List(new[] { getter, setter })).WithLeadingSpace();

			return property.WithAccessorList(accessors);
		}

		/// <summary>
		///     Creates a <see cref="PropertyDeclarationSyntax" /> within an interface.
		/// </summary>
		/// <param name="propertyName">The name of the property.</param>
		/// <param name="propertyType">The type of the property.</param>
		/// <param name="hasGetter">A value indicating whether the property has a getter.</param>
		/// <param name="hasSetter">A value indicating whether the property has a setter.</param>
		public static PropertyDeclarationSyntax InterfaceProperty(string propertyName, string propertyType, bool hasGetter, bool hasSetter)
		{
			Requires.NotNullOrWhitespace(propertyName, () => propertyName);
			Requires.NotNullOrWhitespace(propertyType, () => propertyType);
			Requires.That(hasGetter || hasSetter, "Cannot specify property with neither a getter nor a setter.");

			var type = SyntaxFactory.ParseTypeName(propertyType).WithTrailingSpace();
			var property = SyntaxFactory.PropertyDeclaration(type, propertyName);

			AccessorDeclarationSyntax[] accessors;
			if (hasGetter && hasSetter)
			{
				var getter = Accessor(SyntaxKind.GetAccessorDeclaration, null).WithLeadingSpace();
				var setter = Accessor(SyntaxKind.SetAccessorDeclaration, null).WithLeadingAndTrailingSpace();
				accessors = new[] { getter, setter };
			}
			else if (hasGetter)
				accessors = new[] { Accessor(SyntaxKind.GetAccessorDeclaration, null).WithLeadingAndTrailingSpace() };
			else
				accessors = new[] { Accessor(SyntaxKind.SetAccessorDeclaration, null).WithLeadingAndTrailingSpace() };

			return property.WithAccessorList(SyntaxFactory.AccessorList(SyntaxFactory.List(accessors)).WithLeadingSpace());
		}

		/// <summary>
		///     Creates a <see cref="ParenthesizedLambdaExpressionSyntax" /> or <see cref="SimpleLambdaExpressionSyntax" />.
		/// </summary>
		/// <param name="parameters">The parameters of the lambda function.</param>
		/// <param name="body">The body of the lambda function.</param>
		public static ExpressionSyntax Lambda(IEnumerable<ParameterSyntax> parameters, CSharpSyntaxNode body)
		{
			Requires.NotNull(parameters, () => parameters);
			Requires.NotNull(body, () => body);

			// We construct the lambda with some simple body originally and replace it later on with the real body, as we don't want 
			// to normalize the whitespace of the lambda's body.
			var tempBody = SyntaxFactory.LiteralExpression(SyntaxKind.NullLiteralExpression);

			if (parameters.Count() == 1 && parameters.Single().Type == null)
				return SyntaxFactory.SimpleLambdaExpression(parameters.Single(), tempBody).NormalizeWhitespace().WithBody(body);

			var parameterList = SyntaxFactory.ParameterList(SyntaxFactory.SeparatedList(parameters));
			return SyntaxFactory.ParenthesizedLambdaExpression(parameterList, tempBody).NormalizeWhitespace().WithBody(body);
		}
	}
}