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

namespace SafetySharp.CSharp.Extensions
{
	using System;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with instances derived from <see cref="TypeDeclarationSyntax" />.
	/// </summary>
	internal static class TypeDeclarationExtensions
	{
		/// <summary>
		///     Checks whether <paramref name="classDeclaration" /> is derived from <see cref="Component" />.
		/// </summary>
		/// <param name="classDeclaration">The class declaration that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be to determine the base types.</param>
		internal static bool IsComponentDeclaration(this ClassDeclarationSyntax classDeclaration, SemanticModel semanticModel)
		{
			return classDeclaration.IsDerivedFrom(semanticModel, semanticModel.GetComponentClassSymbol());
		}

		/// <summary>
		///     Checks whether <paramref name="interfaceDeclaration" /> is derived from <see cref="IComponent" />.
		/// </summary>
		/// <param name="interfaceDeclaration">The interface declaration that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be to determine the base types.</param>
		internal static bool IsComponentInterfaceDeclaration(this InterfaceDeclarationSyntax interfaceDeclaration, SemanticModel semanticModel)
		{
			return interfaceDeclaration.IsDerivedFrom(semanticModel, semanticModel.GetComponentInterfaceSymbol());
		}

		/// <summary>
		///     Checks whether <paramref name="typeDeclaration" /> is a directly or indirectly derived from
		///     <paramref name="baseType" />.
		/// </summary>
		/// <param name="typeDeclaration">The type declaration that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be to determine the base types.</param>
		/// <param name="baseType">The base type <paramref name="typeDeclaration" /> should be derived from.</param>
		internal static bool IsDerivedFrom(this TypeDeclarationSyntax typeDeclaration, SemanticModel semanticModel, ITypeSymbol baseType)
		{
			Argument.NotNull(typeDeclaration, () => typeDeclaration);
			Argument.NotNull(semanticModel, () => semanticModel);

			var symbol = (ITypeSymbol)semanticModel.GetDeclaredSymbol(typeDeclaration);
			return symbol.IsDerivedFrom(baseType);
		}

		/// <summary>
		///     Gets the full name of <paramref name="typeDeclaration" /> in the form of 'Namespace1.Namespace2.ClassName+InnerClass'.
		/// </summary>
		/// <param name="typeDeclaration">The type declaration the full name should be returned for.</param>
		/// <param name="semanticModel">The semantic model that should be used to determine the full name.</param>
		internal static string GetFullName(this TypeDeclarationSyntax typeDeclaration, SemanticModel semanticModel)
		{
			Argument.NotNull(typeDeclaration, () => typeDeclaration);
			return ((ITypeSymbol)semanticModel.GetDeclaredSymbol(typeDeclaration)).GetFullName();
		}
	}
}