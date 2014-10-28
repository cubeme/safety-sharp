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

namespace SafetySharp.CSharpCompiler.Roslyn.Symbols
{
	using System;
	using Microsoft.CodeAnalysis;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with <see cref="IMethodSymbol" /> instances.
	/// </summary>
	public static class MethodSymbolExtensions
	{
		/// <summary>
		///     Checks whether <paramref name="methodSymbol" /> overrides <paramref name="overriddenMethod" />.
		/// </summary>
		/// <param name="methodSymbol">The symbol of the method that should be checked.</param>
		/// <param name="overriddenMethod">The symbol of the method that should be overridden.</param>
		[Pure]
		public static bool Overrides([NotNull] this IMethodSymbol methodSymbol, [NotNull] IMethodSymbol overriddenMethod)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(overriddenMethod, () => overriddenMethod);

			if (methodSymbol.Equals(overriddenMethod))
				return true;

			if (!methodSymbol.IsOverride)
				return false;

			if (methodSymbol.OverriddenMethod.Equals(overriddenMethod))
				return true;

			return methodSymbol.OverriddenMethod.Overrides(overriddenMethod);
		}

		/// <summary>
		///     Checks whether <paramref name="methodSymbol" /> overrides the <see cref="Component.Update()" /> method within the
		///     context of the <paramref name="compilation" />.
		/// </summary>
		/// <param name="methodSymbol">The method symbol that should be checked.</param>
		/// <param name="compilation">The compilation that should be used to resolve symbol information.</param>
		[Pure]
		public static bool IsUpdateMethod([NotNull] this IMethodSymbol methodSymbol, [NotNull] Compilation compilation)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(compilation, () => compilation);

			return methodSymbol.Overrides(compilation.GetUpdateMethodSymbol());
		}

		/// <summary>
		///     Checks whether <paramref name="methodSymbol" /> overrides the <see cref="Component.Update()" /> method within the
		///     context of the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="methodSymbol">The method symbol that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve symbol information.</param>
		[Pure]
		public static bool IsUpdateMethod([NotNull] this IMethodSymbol methodSymbol, [NotNull] SemanticModel semanticModel)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(semanticModel, () => semanticModel);

			return methodSymbol.Overrides(semanticModel.GetUpdateMethodSymbol());
		}

		/// <summary>
		///     Checks whether <paramref name="methodSymbol" /> represents a built-in operator of the <see cref="int" />,
		///     <see cref="bool" />, or <see cref="decimal" /> types.
		/// </summary>
		/// <param name="methodSymbol">The method symbol that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve symbol information.</param>
		[Pure]
		public static bool IsBuiltInOperator([NotNull] this IMethodSymbol methodSymbol, [NotNull] SemanticModel semanticModel)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(semanticModel, () => semanticModel);

			return methodSymbol.ContainingType.Equals(semanticModel.GetTypeSymbol<int>()) ||
				   methodSymbol.ContainingType.Equals(semanticModel.GetTypeSymbol<bool>()) ||
				   methodSymbol.ContainingType.Equals(semanticModel.GetTypeSymbol<decimal>());
		}
	}
}