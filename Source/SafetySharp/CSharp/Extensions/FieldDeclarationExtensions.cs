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
	///     Provides extension methods for working with <see cref="FieldDeclarationSyntax" /> instances.
	/// </summary>
	internal static class FieldDeclarationExtensions
	{
		/// <summary>
		///     Checks whether the <paramref name="fieldDeclaration" /> has a <see cref="Component" /> or <see cref="IComponent" />
		///     derived type.
		/// </summary>
		/// <param name="fieldDeclaration">The field declaration that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be used for the check.</param>
		internal static bool IsComponentField(this FieldDeclarationSyntax fieldDeclaration, SemanticModel semanticModel)
		{
			Requires.NotNull(fieldDeclaration, () => fieldDeclaration);
			Requires.NotNull(semanticModel, () => semanticModel);
			Requires.ArgumentSatisfies(fieldDeclaration.Declaration.Variables.Count == 1, () => fieldDeclaration,
							   "Field declaration declares more than one variable.");

			var variable = fieldDeclaration.Declaration.Variables[0];
			var fieldSymbol = (IFieldSymbol)semanticModel.GetDeclaredSymbol(variable);
			var fieldType = fieldSymbol.Type;

			// It is sufficient to check whether the type implements IComponent, as all Component derived classes
			// implement IComponent as well
			var componentInterface = semanticModel.GetComponentInterfaceSymbol();
			return fieldType.IsDerivedFrom(componentInterface) || fieldType.Equals(componentInterface);
		}
	}
}