// The MIT License (MIT)
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

namespace SafetySharp.CSharp
{
	using System;
	using Microsoft.CodeAnalysis;
	using Roslyn.Symbols;
	using Utilities;

	/// <summary>
	///     Represents a port.
	/// </summary>
	public class Port
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="symbol">The symbol that represents the port.</param>
		/// <param name="name">The name of the port.</param>
		/// <param name="isRequiredPort">Indicates whether the port is a required port.</param>
		public Port([NotNull] IMethodSymbol symbol, string name, bool isRequiredPort)
		{
			Requires.NotNull(symbol, () => symbol);
			Requires.NotNullOrWhitespace(name, () => name);

			Symbol = symbol;
			Name = name;
			IsRequiredPort = isRequiredPort;
		}

		/// <summary>
		///     Gets the symbol that represents the port.
		/// </summary>
		public IMethodSymbol Symbol { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the port is a required port.
		/// </summary>
		public bool IsRequiredPort { get; private set; }

		/// <summary>
		///     Gets the name of the port.
		/// </summary>
		public string Name { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the port is a required port.
		/// </summary>
		public bool IsProvidedPort
		{
			get { return !IsRequiredPort; }
		}

		/// <summary>
		///     Checks whether the port is signature-compatible to the <paramref name="methodSymbol" />.
		/// </summary>
		/// <param name="methodSymbol">The method symbol this port should be signature-compatible to.</param>
		public bool IsCompatibleTo([NotNull] IMethodSymbol methodSymbol)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			return methodSymbol.IsSignatureCompatibleTo(Symbol);
		}

		/// <summary>
		///     Checks whether the port is signature-compatible to the <paramref name="other" /> port.
		/// </summary>
		/// <param name="other">The other port this port should be signature-compatible to.</param>
		public bool IsCompatibleTo([NotNull] Port other)
		{
			Requires.NotNull(other, () => other);
			return other.IsCompatibleTo(Symbol);
		}
	}
}