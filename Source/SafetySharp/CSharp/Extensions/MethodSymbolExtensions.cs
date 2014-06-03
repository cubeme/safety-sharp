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
	///     Provides extension methods for working with <see cref="IMethodSymbol" /> instances.
	/// </summary>
	internal static class MethodSymbolExtensions
	{
		/// <summary>
		///     Checks whether the <paramref name="methodSymbol" /> overrides <paramref name="overriddenMethod" />.
		/// </summary>
		/// <param name="methodSymbol">The method symbol that should be checked.</param>
		/// <param name="overriddenMethod">The method <paramref name="methodSymbol" /> should override.</param>
		internal static bool Overrides(this IMethodSymbol methodSymbol, IMethodSymbol overriddenMethod)
		{
			Argument.NotNull(methodSymbol, () => methodSymbol);
			Argument.NotNull(overriddenMethod, () => overriddenMethod);

			if (!methodSymbol.IsOverride)
				return false;

			if (methodSymbol.OverriddenMethod.Equals(overriddenMethod))
				return true;

			return Overrides(methodSymbol.OverriddenMethod, overriddenMethod);
		}

		/// <summary>
		///     Gets the full name of <paramref name="symbol" /> in the form of
		///     'Namespace1.Namespace2.ClassName+InnerClass.MethodName(Namespace1.ClassName1, Namespace2.ClassName2, ...)'.
		/// </summary>
		/// <param name="symbol">The symbol the full name should be returned for.</param>
		internal static string GetFullName(this IMethodSymbol symbol)
		{
			Argument.NotNull(symbol, () => symbol);

			var typeParameters = String.Empty;
			if (symbol.Arity > 0)
				typeParameters = String.Format("<{0}>", String.Join(", ", symbol.TypeArguments.Select(type => type.GetFullName())));

			return String.Format("{3} {0}.{1}{4}({2})", ((ITypeSymbol)symbol.ContainingSymbol).GetFullName(), symbol.Name,
								 String.Join(", ", symbol.Parameters.Select(GetParameterTypeString)), symbol.ReturnType.GetFullName(), typeParameters);
		}

		/// <summary>
		///     Gets the type display string for the <paramref name="parameter" />.
		/// </summary>
		/// <param name="parameter">The parameter the type string should be returned for.</param>
		private static string GetParameterTypeString(IParameterSymbol parameter)
		{
			var refKind = String.Empty;
			switch (parameter.RefKind)
			{
				case RefKind.None:
					break;
				case RefKind.Out:
					refKind = "out ";
					break;
				case RefKind.Ref:
					refKind = "ref ";
					break;
				default:
					Assert.NotReached("Unknown ref kind.");
					break;
			}

			return String.Format("{0}{1}", refKind, parameter.Type.GetFullName());
		}
	}
}