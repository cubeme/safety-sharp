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

namespace Tests.CSharp.Normalization
{
	using System;
	using System.Linq;
	using FluentAssertions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using NUnit.Framework;
	using SafetySharp.CSharp.Normalization;

	[TestFixture]
	internal class TriviaNormalizerTests : CSharpNormalizerTests<TriviaNormalizer>
	{
		private static void ShouldNotContain(SyntaxKind syntaxKind, string csharpCode)
		{
			Normalize(csharpCode)
				.DescendantTrivia()
				.Any(trivia => trivia.CSharpKind() == syntaxKind)
				.Should()
				.BeFalse();
		}

		[Test]
		public void RemoveMultiLineComment()
		{
			ShouldNotContain(SyntaxKind.MultiLineCommentTrivia, @"
/* Comment 1 */
class Test
{
	/* Comment 2
	   Second line
	*/
	bool M(int i /* = 3 */)
	{
		/* Comment 3
		return true;
		*/
		return false; /* Comment 4 */
		/* Comment 5
        Comment 6 */
	}
}
");
		}

		[Test]
		public void RemoveDocComment()
		{
			ShouldNotContain(SyntaxKind.SingleLineDocumentationCommentTrivia, @"
/// <summary>
///     Some Test class
/// </summary>
/// <typeparam name=""T"">Some type.</typeparam>
/// <remarks>
///     Obviously, this is just a test.
/// </remarks>
class Test<T>
{
	/// <summary>
	///		Test class.
	///     Next line.
	/// </summary>
	/// <param name=""test"">Test</param>
	bool M(int test)
	{
		return false;
	}
}
");
		}

		[Test]
		public void RemoveSingleLineComment()
		{
			ShouldNotContain(SyntaxKind.SingleLineCommentTrivia, @"
// Comment 1
class Test
{
	// Comment 2
	bool M(int i)
	{
		// Comment 4
		// return true;
		return false; // Comment 5
		// Comment 6
	}
}
");
		}
	}
}