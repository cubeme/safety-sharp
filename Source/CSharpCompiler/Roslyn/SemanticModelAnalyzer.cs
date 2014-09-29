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
	using Microsoft.CodeAnalysis.Diagnostics;
	using Utilities;

	/// <summary>
	///     A base class for SafetySharp C# <see cref="SemanticModel" /> analyzers.
	/// </summary>
	public abstract class SemanticModelAnalyzer : CSharpAnalyzer, ISemanticModelAnalyzer
	{
		/// <summary>
		///     Analyzes the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semanticModel that should be analyzed.</param>
		/// <param name="addDiagnostic">The delegate that should be used to emit diagnostics.</param>
		/// <param name="options">A set of options passed in by the host.</param>
		/// <param name="cancellationToken">The token that should be checked for cancelling the analysis.</param>
		public void AnalyzeSemanticModel([NotNull] SemanticModel semanticModel, [NotNull] Action<Diagnostic> addDiagnostic,
										 AnalyzerOptions options, CancellationToken cancellationToken)
		{
			Requires.NotNull(semanticModel, () => semanticModel);
			Requires.NotNull(addDiagnostic, () => addDiagnostic);

			DiagnosticCallback = addDiagnostic;
			Analyze(semanticModel);
		}

		/// <summary>
		///     Analyzes the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model that should be analyzed.</param>
		protected abstract void Analyze([NotNull] SemanticModel semanticModel);

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