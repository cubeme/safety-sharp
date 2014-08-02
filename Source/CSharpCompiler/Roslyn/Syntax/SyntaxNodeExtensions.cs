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
	using Symbols;
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with <see cref="SyntaxNode" /> instances.
	/// </summary>
	public static class SyntaxNodeExtensions
	{
		/// <summary>
		///     Gets a list of descendant syntax nodes of type <typeparamref name="T" /> in prefix document order.
		/// </summary>
		/// <typeparam name="T">The type of the syntax nodes that should be returned.</typeparam>
		/// <param name="syntaxNode">The syntax node whose descendents should be returned.</param>
		public static IEnumerable<T> Descendants<T>(this SyntaxNode syntaxNode)
			where T : SyntaxNode
		{
			Requires.NotNull(syntaxNode, () => syntaxNode);
			return syntaxNode.DescendantNodes().OfType<T>();
		}

		/// <summary>
		///     Gets a list of descendant syntax nodes (including <paramref name="syntaxNode" />) of type <typeparamref name="T" /> in
		///     prefix document order.
		/// </summary>
		/// <typeparam name="T">The type of the syntax nodes that should be returned.</typeparam>
		/// <param name="syntaxNode">The syntax node whose descendents should be returned.</param>
		public static IEnumerable<T> DescendantsAndSelf<T>(this SyntaxNode syntaxNode)
			where T : SyntaxNode
		{
			Requires.NotNull(syntaxNode, () => syntaxNode);
			return syntaxNode.DescendantNodesAndSelf().OfType<T>();
		}

		/// <summary>
		///     Gets the symbol referenced by <paramref name="syntaxNode" /> within the context of the <paramref name="semanticModel" />
		///     .
		/// </summary>
		/// <typeparam name="T">The expected type of the referenced symbol.</typeparam>
		/// <param name="syntaxNode">The node the referenced symbol should be returned for.</param>
		/// <param name="semanticModel">The semantic model that should be used to determine the referenced symbol.</param>
		public static T GetReferencedSymbol<T>(this SyntaxNode syntaxNode, SemanticModel semanticModel)
			where T : class, ISymbol
		{
			Requires.NotNull(syntaxNode, () => syntaxNode);
			Requires.NotNull(semanticModel, () => semanticModel);

			var symbolInfo = semanticModel.GetSymbolInfo(syntaxNode);
			Requires.That(symbolInfo.Symbol != null, "Unable to determine the symbol referenced by syntax node '{0}'.", syntaxNode);

			var symbol = symbolInfo.Symbol as T;
			Requires.That(symbol != null, "Expected a symbol of type '{0}'. However, the actual symbol type for syntax node '{1}' is '{2}'.",
						  typeof(T).FullName, syntaxNode, symbolInfo.Symbol.GetType().FullName);

			return symbol;
		}

		/// <summary>
		///     Checks whether the <paramref name="syntaxNode" /> is marked with an attribute of type <typeparamref name="T" /> within
		///     the context of the <paramref name="semanticModel" />. This method only succeeds if <paramref name="syntaxNode" />
		///     declares a symbol.
		/// </summary>
		/// <typeparam name="T">The type of the attribute <paramref name="syntaxNode" /> should be marked with.</typeparam>
		/// <param name="syntaxNode">The syntax node that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve symbol information.</param>
		public static bool HasAttribute<T>(this SyntaxNode syntaxNode, SemanticModel semanticModel)
			where T : Attribute
		{
			Requires.NotNull(syntaxNode, () => syntaxNode);
			Requires.NotNull(semanticModel, () => semanticModel);

			return syntaxNode.GetReferencedSymbol<ISymbol>(semanticModel).HasAttribute<T>(semanticModel);
		}
	}
}