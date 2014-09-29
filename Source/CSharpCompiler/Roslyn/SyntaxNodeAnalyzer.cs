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

namespace SafetySharp.CSharpCompiler.Roslyn
{
	using System;
	using System.Threading;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Syntax;
	using Utilities;

	/// <summary>
	///     A base class for SafetySharp C# <see cref="SyntaxNode" /> analyzers.
	/// </summary>
	public abstract class SyntaxNodeAnalyzer<T> : CSharpAnalyzer, ISyntaxTreeAnalyzer
		where T : CSharpSyntaxNode
	{
		/// <summary>
		///     Analyzes the <paramref name="syntaxTree" />.
		/// </summary>
		/// <param name="syntaxTree">The syntaxTree that should be analyzed.</param>
		/// <param name="addDiagnostic">A delegate that should be used to emit diagnostics.</param>
		/// <param name="options">A set of options passed in by the host.</param>
		/// <param name="cancellationToken">A token that should be checked for cancelling the analysis.</param>
		public void AnalyzeSyntaxTree([NotNull] SyntaxTree syntaxTree, [NotNull] Action<Diagnostic> addDiagnostic,
									  AnalyzerOptions options, CancellationToken cancellationToken)
		{
			Requires.NotNull(syntaxTree, () => syntaxTree);
			Requires.NotNull(addDiagnostic, () => addDiagnostic);

			DiagnosticCallback = addDiagnostic;
			foreach (var node in syntaxTree.DescendantsAndSelf<T>())
				Analyze(node);
		}

		/// <summary>
		///     Analyzes the <paramref name="syntaxNode" />.
		/// </summary>
		/// <param name="syntaxNode">The syntax node that should be analyzed.</param>
		protected abstract void Analyze([NotNull] T syntaxNode);

		/// <summary>
		///     Emits a diagnostic for <paramref name="syntaxNode" /> using the <paramref name="messageArgs" /> to format the diagnostic
		///     message.
		/// </summary>
		/// <param name="syntaxNode">The syntax node the diagnostic is emitted for.</param>
		/// <param name="messageArgs">The arguments for formatting the diagnostic message.</param>
		protected void EmitDiagnostic([NotNull] SyntaxNode syntaxNode, params object[] messageArgs)
		{
			DiagnosticCallback(Diagnostic.Create(Descriptor, syntaxNode.GetLocation(), messageArgs));
		}
	}
}