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
	using System.Collections.Immutable;
	using System.Threading;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Utilities;

	/// <summary>
	///     A base class for SafetySharp C# <see cref="ISymbol" /> analyzers.
	/// </summary>
	/// <typeparam name="T">The type of the analyzed symbols</typeparam>
	public abstract class SymbolAnalyzer<T> : CSharpAnalyzer, ISymbolAnalyzer
		where T : class, ISymbol
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="symbolKind">The kind of the symbol analyzed by this analyzer.</param>
		/// <param name="symbolKinds">The additional kinds of symbols analyzed by this analyzer.</param>
		protected SymbolAnalyzer(SymbolKind symbolKind, params SymbolKind[] symbolKinds)
		{
			Requires.NotNull(symbolKinds, () => symbolKinds);
			SymbolKindsOfInterest = ImmutableArray.Create(symbolKind).AddRange(symbolKinds);
		}

		/// <summary>
		///     Called for each declared symbol in the compilation where the symbol's kind is an element of
		///     <see cref="SymbolKindsOfInterest" />.
		/// </summary>
		/// <param name="symbol">The symbol that should be analyzed.</param>
		/// <param name="compilation">The compilation the symbol is declared in.</param>
		/// <param name="addDiagnostic">A delegate to be used to emit diagnostics.</param>
		/// <param name="options">A set of options passed in by the host.</param>
		/// <param name="cancellationToken">A token for cancelling the computation.</param>
		public void AnalyzeSymbol([NotNull] ISymbol symbol, [NotNull] Compilation compilation, [NotNull] Action<Diagnostic> addDiagnostic,
								  AnalyzerOptions options, CancellationToken cancellationToken)
		{
			Requires.NotNull(symbol, () => symbol);
			Requires.NotNull(compilation, () => compilation);
			Requires.NotNull(addDiagnostic, () => addDiagnostic);

			DiagnosticCallback = addDiagnostic;
			Analyze((T)symbol, compilation);
		}

		/// <summary>
		///     Gets the set of symbol kinds supported by the analyzer.
		/// </summary>
		public ImmutableArray<SymbolKind> SymbolKindsOfInterest { get; private set; }

		/// <summary>
		///     Analyzes the <paramref name="symbol" />.
		/// </summary>
		/// <param name="symbol">The symbol that should be analyzed.</param>
		/// <param name="compilation">The compilation the symbol is declared in.</param>
		protected abstract void Analyze([NotNull] T symbol, [NotNull] Compilation compilation);

		/// <summary>
		///     Emits a diagnostic for <paramref name="symbol" /> using the <paramref name="messageArgs" /> to format the diagnostic
		///     message.
		/// </summary>
		/// <param name="symbol">The symbol the diagnostic is emitted for.</param>
		/// <param name="messageArgs">The arguments for formatting the diagnostic message.</param>
		protected void EmitDiagnostic([NotNull] ISymbol symbol, params object[] messageArgs)
		{
			DiagnosticCallback(Diagnostic.Create(Descriptor, symbol.Locations[0], messageArgs));
		}
	}
}