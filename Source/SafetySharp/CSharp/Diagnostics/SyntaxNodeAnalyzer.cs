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

namespace SafetySharp.CSharp.Diagnostics
{
	using System;
	using System.Linq;
	using System.Threading;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Utilities;

	/// <summary>
	///     A base class for syntax node analyzers.
	/// </summary>
	public abstract class SyntaxNodeAnalyzer<T> : CSharpAnalyzer, ISyntaxTreeAnalyzer
		where T : CSharpSyntaxNode
	{
		/// <summary>
		///     Analyzes a syntax tree of a compilation.
		/// </summary>
		/// <param name="tree">The tree that should be analyzed.</param>
		/// <param name="addDiagnostic">A delegate that should be used to emit diagnostics.</param>
		/// <param name="cancellationToken">A token that should be checked for cancelling the analysis.</param>
		public void AnalyzeSyntaxTree(SyntaxTree tree, Action<Diagnostic> addDiagnostic, CancellationToken cancellationToken)
		{
			Assert.ArgumentNotNull(tree, () => tree);
			Assert.ArgumentNotNull(addDiagnostic, () => addDiagnostic);

			foreach (var node in tree.GetRoot().DescendantNodesAndSelf().OfType<T>())
				Analyze(node, (locationNode, args) => addDiagnostic(Diagnostic.Create(Descriptor, locationNode.GetLocation(), args)), cancellationToken);
		}

		/// <summary>
		///     Analyzes a syntax node.
		/// </summary>
		/// <param name="node">The syntax node that should be analyzed.</param>
		/// <param name="addDiagnostic">A delegate that should be used to emit diagnostics.</param>
		/// <param name="cancellationToken">A token that should be checked for cancelling the analysis.</param>
		protected abstract void Analyze(T node, AddDiagnosticCallback addDiagnostic, CancellationToken cancellationToken);

		/// <summary>
		///     Represents a callback that emits a diagnostic.
		/// </summary>
		/// <param name="locationNode">The node that causes the diagnostic to be emitted.</param>
		/// <param name="messageArgs">The arguments for formatting the diagnostic message.</param>
		protected delegate void AddDiagnosticCallback(CSharpSyntaxNode locationNode, params object[] messageArgs);
	}
}