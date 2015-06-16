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

namespace SafetySharp.Compiler.Analyzers
{
	using System;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Modeling.Faults;
	using Roslyn;
	using Roslyn.Symbols;

	/// <summary>
	///     Ensures that all faults are directly derived from <see cref="Fault" />. Fault inheritance is currently not supported.
	/// </summary>
	[DiagnosticAnalyzer(LanguageNames.CSharp), UsedImplicitly]
	public sealed class FaultAnalyzer : Analyzer
	{
		/// <summary>
		///     The error diagnostic emitted by the analyzer.
		/// </summary>
		private static readonly DiagnosticInfo _unsupportedFaultInheritance = DiagnosticInfo.Error(
			DiagnosticIdentifier.UnsupportedFaultInheritance,
			String.Format("Faults must directly inherit '{0}'. Fault inheritance is currently unsupported.", typeof(Fault).FullName),
			String.Format("Fault '{{0}}' must be directly derived from '{0}'. Fault inheritance is currently unsupported.", typeof(Fault).FullName));

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public FaultAnalyzer()
			: base(_unsupportedFaultInheritance)
		{
		}

		/// <summary>
		///     Called once at session start to register actions in the analysis context.
		/// </summary>
		/// <param name="context">The analysis context that should be used to register analysis actions.</param>
		public override void Initialize(AnalysisContext context)
		{
			context.RegisterSymbolAction(Analyze, SymbolKind.NamedType);
		}

		/// <summary>
		///     Performs the analysis.
		/// </summary>
		/// <param name="context">The context in which the analysis should be performed.</param>
		private static void Analyze(SymbolAnalysisContext context)
		{
			var compilation = context.Compilation;
			var symbol = context.Symbol as ITypeSymbol;

			if (symbol == null)
				return;

			if (!symbol.IsDerivedFromFault(compilation))
				return;

			if (!symbol.BaseType.Equals(compilation.GetFaultClassSymbol()))
				_unsupportedFaultInheritance.Emit(context, symbol, symbol.ToDisplayString());
		}
	}
}