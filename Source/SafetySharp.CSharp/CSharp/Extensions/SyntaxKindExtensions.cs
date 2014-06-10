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
	using System.Text;
	using Microsoft.CodeAnalysis.CSharp;

	/// <summary>
	///     Provides extension methods for working with <see cref="SyntaxKind" /> instances.
	/// </summary>
	internal static class SyntaxKindExtensions
	{
		/// <summary>
		///     Generates a user-friendly description for <paramref name="syntaxKind" />.
		/// </summary>
		/// <param name="syntaxKind">The syntax kind the description should be generated for.</param>
		internal static string ToDescription(this SyntaxKind syntaxKind)
		{
			var nodeKind = syntaxKind.ToString();
			var name = new StringBuilder();

			name.Append(Char.ToLower(nodeKind[0]));
			foreach (var c in nodeKind.Skip(1))
			{
				if (Char.IsUpper(c))
					name.AppendFormat(" {0}", Char.ToLower(c));
				else
					name.Append(c);
			}

			return name.ToString();
		}
	}
}