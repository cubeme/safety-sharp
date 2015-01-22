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

namespace SafetySharp.CSharp.Roslyn
{
	using System;
	using Microsoft.CodeAnalysis;
	using Utilities;

	/// <summary>
	///     Synthesizes unique variable or type identifier names for specific locations within a C# <see cref="SyntaxTree" />.
	/// </summary>
	public static class IdentifierNameSynthesizer
	{
		/// <summary>
		///     Gets a value indicating whether <paramref name="name" /> is a synthesized name.
		/// </summary>
		/// <param name="name">The name that should be checked.</param>
		public static bool IsSynthesized(string name)
		{
			return name.StartsWith("__") && name.EndsWith("__");
		}

		/// <summary>
		///     Gets a value indicating whether <paramref name="identifier" /> is a synthesized name.
		/// </summary>
		/// <param name="identifier">The identifier that should be checked.</param>
		public static bool IsSynthesized(SyntaxToken identifier)
		{
			return IsSynthesized(identifier.ValueText);
		}

		/// <summary>
		///     Converts <paramref name="name" /> to a synthesized name.
		/// </summary>
		/// <param name="name">The name that should be converted.</param>
		public static string ToSynthesizedName(string name)
		{
			Requires.NotNullOrWhitespace(name, () => name);
			Requires.ArgumentSatisfies(!IsSynthesized(name), () => name, "The name has already been escaped.");

			return String.Format("__{0}__", name);
		}
	}
}