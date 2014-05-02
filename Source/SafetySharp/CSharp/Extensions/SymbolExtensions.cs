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
	///     Provides extension methods for working with <see cref="ISymbol" /> instances.
	/// </summary>
	internal static class SymbolExtensions
	{
		/// <summary>
		///     Gets the full name of <paramref name="symbol" /> in the form of 'Namespace1.Namespace2.ClassName+InnerClass'.
		/// </summary>
		/// <param name="symbol">The symbol the full name should be returned for.</param>
		internal static string GetFullName(this ISymbol symbol)
		{
			Argument.NotNull(symbol, () => symbol);

			if (symbol.ContainingNamespace.IsGlobalNamespace && symbol.ContainingType == null)
				return symbol.Name;

			if (symbol.ContainingType != null)
				return String.Format("{0}+{1}", GetFullName(symbol.ContainingType), symbol.Name);

			return String.Format("{0}.{1}", GetFullName(symbol.ContainingNamespace), symbol.Name);
		}
	}
}