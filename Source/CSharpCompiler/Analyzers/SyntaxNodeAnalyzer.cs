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

namespace SafetySharp.CSharpCompiler.Analyzers
{
	using System;
	using System.Threading;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Roslyn.Syntax;
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
		/// <param name="cancellationToken">A token that should be checked for cancelling the analysis.</param>
		public void AnalyzeSyntaxTree(SyntaxTree syntaxTree, Action<Diagnostic> addDiagnostic, CancellationToken cancellationToken)
		{
			Requires.NotNull(syntaxTree, () => syntaxTree);
			Requires.NotNull(addDiagnostic, () => addDiagnostic);

			DiagnosticEmitter<SyntaxNode> emitter =
				(locationNode, args) => addDiagnostic(Diagnostic.Create(Descriptor, locationNode.GetLocation(), args));

			foreach (var node in syntaxTree.DescendantsAndSelf<T>())
				Analyze(node, emitter, cancellationToken);
		}

		/// <summary>
		///     Analyzes the <paramref name="syntaxNode" />.
		/// </summary>
		/// <param name="syntaxNode">The syntax node that should be analyzed.</param>
		/// <param name="emitDiagnostic">The delegate that should be used to emit diagnostics.</param>
		/// <param name="cancellationToken">The token that should be checked for cancelling the analysis.</param>
		protected abstract void Analyze(T syntaxNode, DiagnosticEmitter<SyntaxNode> emitDiagnostic, CancellationToken cancellationToken);
	}
}