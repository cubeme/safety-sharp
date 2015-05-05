﻿// The MIT License (MIT)
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

namespace SafetySharp.CSharp.Roslyn.Syntax
{
	using System;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;
	using Symbols;
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with <see cref="BaseTypeDeclarationSyntax" /> instances.
	/// </summary>
	public static class BaseTypeDeclarationExtensions
	{
		/// <summary>
		///     Gets the <see cref="INamedTypeSymbol" /> declared by <paramref name="typeDeclaration" /> within the context of the
		///     <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="typeDeclaration">The type declaration the declared symbol should be returned for.</param>
		/// <param name="semanticModel">The semantic model that should be used to determine the declared symbol.</param>
		[Pure, NotNull]
		public static INamedTypeSymbol GetTypeSymbol([NotNull] this BaseTypeDeclarationSyntax typeDeclaration,
													 [NotNull] SemanticModel semanticModel)
		{
			Requires.NotNull(typeDeclaration, () => typeDeclaration);
			Requires.NotNull(semanticModel, () => semanticModel);

			var symbol = semanticModel.GetDeclaredSymbol(typeDeclaration);
			Assert.NotNull(symbol, "Unable to determine type symbol of type declaration '{0}'.", typeDeclaration);

			return symbol;
		}

		/// <summary>
		///     Checks whether <paramref name="typeDeclaration" /> is directly or indirectly derived from the
		///     <paramref name="baseType" />
		///     interface or class within the context of the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="typeDeclaration">The type declaration that should be checked.</param>
		/// <param name="semanticModel">
		///     The semantic model that should be used to resolve the type symbol of the <paramref name="typeDeclaration" />.
		/// </param>
		/// <param name="baseType">The base type interface or class that <paramref name="typeDeclaration" /> should be derived from.</param>
		[Pure]
		public static bool IsDerivedFrom([NotNull] this BaseTypeDeclarationSyntax typeDeclaration, [NotNull] SemanticModel semanticModel,
										 [NotNull] ITypeSymbol baseType)
		{
			Requires.NotNull(typeDeclaration, () => typeDeclaration);
			Requires.NotNull(semanticModel, () => semanticModel);
			Requires.NotNull(baseType, () => baseType);

			return typeDeclaration.GetTypeSymbol(semanticModel).IsDerivedFrom(baseType);
		}

		/// <summary>
		///     Checks whether <paramref name="typeDeclaration" /> is directly or indirectly derived from the <see cref="Component" />
		///     class within the context of the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="typeDeclaration">The type declaration that should be checked.</param>
		/// <param name="semanticModel">
		///     The semantic model that should be used to resolve the type symbol for the <see cref="Component" /> class.
		/// </param>
		[Pure]
		public static bool IsDerivedFromComponent([NotNull] this BaseTypeDeclarationSyntax typeDeclaration, [NotNull] SemanticModel semanticModel)
		{
			Requires.NotNull(typeDeclaration, () => typeDeclaration);
			Requires.NotNull(semanticModel, () => semanticModel);

			return typeDeclaration.IsDerivedFrom(semanticModel, semanticModel.GetComponentClassSymbol());
		}

		/// <summary>
		///     Checks whether <paramref name="typeDeclaration" /> directly or indirectly implements the <see cref="IComponent" />
		///     interface within the context of the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="typeDeclaration">The type declaration that should be checked.</param>
		/// <param name="semanticModel">
		///     The semantic model that should be used to resolve the type symbol for the <see cref="IComponent" /> interface.
		/// </param>
		[Pure]
		public static bool ImplementsIComponent([NotNull] this BaseTypeDeclarationSyntax typeDeclaration, [NotNull] SemanticModel semanticModel)
		{
			Requires.NotNull(typeDeclaration, () => typeDeclaration);
			Requires.NotNull(semanticModel, () => semanticModel);

			return typeDeclaration.IsDerivedFrom(semanticModel, semanticModel.GetComponentInterfaceSymbol());
		}
	}
}