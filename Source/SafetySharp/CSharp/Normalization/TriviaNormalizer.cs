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

namespace SafetySharp.CSharp.Normalization
{
	using System;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Utilities;

	/// <summary>
	///     Removes all unnecessary trivia from the C# code.
	/// </summary>
	public class TriviaNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     Replaces the trivia by a single space if it is any other whitespace trivia or a comment.
		/// </summary>
		/// <param name="trivia">The trivia that should be replaced.</param>
		/// <remarks>
		///     Obviously, this normalizer is not required for correctness. For heavily documented models, however, it decreases
		///     the size of the generated assembly and might somewhat speed up parsing at runtime.
		/// </remarks>
		public override SyntaxTrivia VisitTrivia(SyntaxTrivia trivia)
		{
			switch (trivia.CSharpKind())
			{
				case SyntaxKind.EndOfLineTrivia:
				case SyntaxKind.SingleLineCommentTrivia:
				case SyntaxKind.MultiLineCommentTrivia:
				case SyntaxKind.SingleLineDocumentationCommentTrivia:
				case SyntaxKind.WhitespaceTrivia:
				case SyntaxKind.MultiLineDocumentationCommentTrivia:
					return SyntaxFactory.Space;
				case SyntaxKind.DisabledTextTrivia:
				case SyntaxKind.DocumentationCommentExteriorTrivia:
				case SyntaxKind.PreprocessingMessageTrivia:
				case SyntaxKind.IfDirectiveTrivia:
				case SyntaxKind.ElifDirectiveTrivia:
				case SyntaxKind.ElseDirectiveTrivia:
				case SyntaxKind.EndIfDirectiveTrivia:
				case SyntaxKind.RegionDirectiveTrivia:
				case SyntaxKind.EndRegionDirectiveTrivia:
				case SyntaxKind.DefineDirectiveTrivia:
				case SyntaxKind.UndefDirectiveTrivia:
				case SyntaxKind.ErrorDirectiveTrivia:
				case SyntaxKind.WarningDirectiveTrivia:
				case SyntaxKind.LineDirectiveTrivia:
				case SyntaxKind.PragmaWarningDirectiveTrivia:
				case SyntaxKind.PragmaChecksumDirectiveTrivia:
				case SyntaxKind.ReferenceDirectiveTrivia:
				case SyntaxKind.BadDirectiveTrivia:
				case SyntaxKind.SkippedTokensTrivia:
					return trivia;
				default:
					Assert.NotReached("Unsupported C# trivia kind: '{0}'.", trivia.CSharpKind());
					return trivia;
			}
		}
	}
}