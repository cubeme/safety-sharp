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
	using Microsoft.CodeAnalysis;
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with <see cref="INamespaceOrTypeSymbol" /> instances.
	/// </summary>
	internal static class NamespaceOrTypeSymbolExtensions
	{
		/// <summary>
		///     Gets the full name of <paramref name="symbol" /> in the form of 'Namespace1.Namespace2.ClassName+InnerClass'.
		/// </summary>
		/// <param name="symbol">The symbol the full name should be returned for.</param>
		internal static string GetFullName(this INamespaceOrTypeSymbol symbol)
		{
			Requires.NotNull(symbol, () => symbol);

			var arraySymbol = symbol as IArrayTypeSymbol;
			if (arraySymbol != null)
				return String.Format("{0}[{1}]", arraySymbol.ElementType.GetFullName(),
									 String.Join(",", Enumerable.Range(0, arraySymbol.Rank).Select(r => String.Empty)));

			var typePrefix = String.Empty;
			if (!symbol.ContainingNamespace.IsGlobalNamespace)
					typePrefix = symbol.ContainingNamespace.GetFullName() + ".";

			var namedTypeSymbol = symbol as INamedTypeSymbol;
			if (namedTypeSymbol == null)
				return String.Format("{0}{1}", typePrefix, symbol.Name);

			if (symbol.ContainingType != null)
				typePrefix = symbol.ContainingType.GetFullName() + "+";

			var typeParameters = String.Empty;
			if (namedTypeSymbol.Arity > 0)
				typeParameters = String.Format("<{0}>", String.Join(", ", namedTypeSymbol.TypeArguments.Select(type => type.GetFullName())));

			return String.Format("{0}{1}{2}", typePrefix, namedTypeSymbol.Name, typeParameters);
		}
	}
}