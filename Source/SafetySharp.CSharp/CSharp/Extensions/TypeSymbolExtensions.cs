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
	using System.Linq;
	using Metamodel.Types;
	using Microsoft.CodeAnalysis;
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with <see cref="ITypeSymbol" /> instances.
	/// </summary>
	internal static class TypeSymbolExtensions
	{
		/// <summary>
		///     Checks whether <paramref name="typeSymbol" /> is directly or indirectly derived from the <paramref name="baseType" />
		///     interface or class.
		/// </summary>
		/// <param name="typeSymbol">The type symbol that should be checked.</param>
		/// <param name="baseType">The class or interface base type that <paramref name="typeSymbol" /> should be derived from.</param>
		internal static bool IsDerivedFrom(this ITypeSymbol typeSymbol, ITypeSymbol baseType)
		{
			Requires.NotNull(typeSymbol, () => typeSymbol);
			Requires.NotNull(baseType, () => baseType);

			// Check whether any of the interfaces or their bases match baseType
			if (baseType.TypeKind == TypeKind.Interface && (typeSymbol.Interfaces.Any(i => i.Equals(baseType) || IsDerivedFrom(i, baseType))))
				return true;

			// We've reached the top of the inheritance chain without finding baseType
			if (typeSymbol.BaseType == null)
				return false;

			// Check whether the base matches baseType
			if (baseType.TypeKind == TypeKind.Class && typeSymbol.BaseType.Equals(baseType))
				return true;

			// Recursively check whether the base
			return IsDerivedFrom(typeSymbol.BaseType, baseType);
		}

		/// <summary>
		///     Converts the C# <paramref name="symbol" /> to a corresponding <see cref="TypeSymbol" /> instance.
		/// </summary>
		/// <param name="symbol">The C# symbol that should be converted.</param>
		/// <param name="semanticModel">The semantic model that should be used for the conversion.</param>
		internal static TypeSymbol ToTypeSymbol(this ITypeSymbol symbol, SemanticModel semanticModel)
		{
			Requires.NotNull(symbol, () => symbol);
			Requires.NotNull(semanticModel, () => semanticModel);

			switch (symbol.SpecialType)
			{
				case SpecialType.None:
					Assert.NotReached("Type '{0}' not yet supported.", symbol);
					return null;
				case SpecialType.System_Boolean:
					return TypeSymbol.Boolean;
				case SpecialType.System_Decimal:
					return TypeSymbol.Decimal;
				case SpecialType.System_Int32:
					return TypeSymbol.Integer;
				case SpecialType.System_Void:
					return TypeSymbol.Void;
				default:
					Assert.NotReached("Unsupported C# type '{0}'.", symbol);
					return null;
			}
		}
	}
}