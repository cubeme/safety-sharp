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
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with <see cref="ITypeSymbol" /> instances.
	/// </summary>
	internal static class TypeSymbolExtensions
	{
		/// <summary>
		///     Checks whether <paramref name="typeSymbol" /> is directly or indirectly derived from <paramref name="baseType." />
		/// </summary>
		/// <param name="typeSymbol">The type symbol that should be checked.</param>
		/// <param name="baseType">The base type <paramref name="typeSymbol" /> should be derived from.</param>
		internal static bool IsDerivedFrom(this ITypeSymbol typeSymbol, ITypeSymbol baseType)
		{
			Argument.NotNull(typeSymbol, () => typeSymbol);
			Argument.NotNull(baseType, () => baseType);

			// We've reached the top of the inheritance chain (namely, System.Object) without finding the base type we've searched for
			if (typeSymbol.BaseType == null)
				return false;

			// Use a type name comparison to determine whether the type symbol's base type is the searched for type
			if (typeSymbol.BaseType.Equals(baseType))
				return true;

			return IsDerivedFrom(typeSymbol.BaseType, baseType);
		}
	}
}