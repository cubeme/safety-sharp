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
	using System.Collections.Immutable;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Utilities;

	/// <summary>
	///     A base class for SafetySharp C# code analyzers.
	/// </summary>
	public abstract class CSharpAnalyzer : DiagnosticAnalyzer
	{
		/// <summary>
		///     The prefix that is used for all diagnostic identifiers.
		/// </summary>
		public const string Prefix = "SS";

		/// <summary>
		///     The category that is used for all diagnostics.
		/// </summary>
		public const string Category = "SafetySharp";

		/// <summary>
		///     The set of descriptors for the diagnostics that this analyzer is capable of producing.
		/// </summary>
		private ImmutableArray<DiagnosticDescriptor> _supportedDiagnostics;

		/// <summary>
		///     Gets the descriptor for the diagnostic emitted by the analyzer.
		/// </summary>
		protected DiagnosticDescriptor Descriptor { get; private set; }

		/// <summary>
		///     Returns a set of descriptors for the diagnostics that this analyzer is capable of producing.
		/// </summary>
		public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics
		{
			get { return _supportedDiagnostics; }
		}

		/// <summary>
		///     Describes the error diagnostic of the analyzer.
		/// </summary>
		/// <param name="identifier">The identifier of the analyzer's diagnostic.</param>
		/// <param name="description">The description of the diagnostic.</param>
		/// <param name="messageFormat">The message format of the diagnostic.</param>
		protected void Error(int identifier, [NotNull] string description, [NotNull] string messageFormat)
		{
			SetDescriptor(identifier, description, messageFormat, DiagnosticSeverity.Error);
		}

		/// <summary>
		///     Describes the error diagnostic of the analyzer.
		/// </summary>
		/// <param name="identifier">The identifier of the analyzer's diagnostic.</param>
		/// <param name="description">The description of the diagnostic.</param>
		/// <param name="messageFormat">The message format of the diagnostic.</param>
		protected void Warning(int identifier, [NotNull] string description, [NotNull] string messageFormat)
		{
			SetDescriptor(identifier, description, messageFormat, DiagnosticSeverity.Warning);
		}

		/// <summary>
		///     Describes the error diagnostic of the analyzer.
		/// </summary>
		/// <param name="identifier">The identifier of the analyzer's diagnostic.</param>
		/// <param name="description">The description of the diagnostic.</param>
		/// <param name="messageFormat">The message format of the diagnostic.</param>
		/// <param name="severity">The severity of the diagnostic.</param>
		private void SetDescriptor(int identifier, [NotNull] string description, [NotNull] string messageFormat, DiagnosticSeverity severity)
		{
			Requires.That(Descriptor == null, "A descriptor has already been set.");
			Requires.NotNullOrWhitespace(description, () => description);
			Requires.NotNullOrWhitespace(messageFormat, () => messageFormat);
			Requires.InRange(severity, () => severity);

			Descriptor = new DiagnosticDescriptor(Prefix + identifier, description, messageFormat, Category, severity, true);
			_supportedDiagnostics = ImmutableArray.Create(Descriptor);
		}

		/// <summary>
		///     Emits a diagnostic for <paramref name="syntaxNode" /> using the <paramref name="messageArgs" /> to format the
		///     diagnostic message.
		/// </summary>
		/// <param name="context">The context in which the diagnostic should be emitted.</param>
		/// <param name="syntaxNode">The syntax node the diagnostic is emitted for.</param>
		/// <param name="messageArgs">The arguments for formatting the diagnostic message.</param>
		protected void EmitDiagnostic(SyntaxNodeAnalysisContext context, [NotNull] SyntaxNode syntaxNode, params object[] messageArgs)
		{
			context.ReportDiagnostic(Diagnostic.Create(Descriptor, syntaxNode.GetLocation(), messageArgs));
		}

		/// <summary>
		///     Emits a diagnostic for <paramref name="syntaxNode" /> using the <paramref name="messageArgs" /> to format the
		///     diagnostic message.
		/// </summary>
		/// <param name="context">The context in which the diagnostic should be emitted.</param>
		/// <param name="syntaxNode">The syntax node the diagnostic is emitted for.</param>
		/// <param name="messageArgs">The arguments for formatting the diagnostic message.</param>
		protected void EmitDiagnostic(SyntaxTreeAnalysisContext context, [NotNull] SyntaxNode syntaxNode, params object[] messageArgs)
		{
			context.ReportDiagnostic(Diagnostic.Create(Descriptor, syntaxNode.GetLocation(), messageArgs));
		}

		/// <summary>
		///     Emits a diagnostic for <paramref name="syntaxToken" /> using the <paramref name="messageArgs" /> to format the
		///     diagnostic message.
		/// </summary>
		/// <param name="context">The context in which the diagnostic should be emitted.</param>
		/// <param name="syntaxToken">The syntax token the diagnostic is emitted for.</param>
		/// <param name="messageArgs">The arguments for formatting the diagnostic message.</param>
		protected void EmitDiagnostic(SyntaxTreeAnalysisContext context, SyntaxToken syntaxToken, params object[] messageArgs)
		{
			context.ReportDiagnostic(Diagnostic.Create(Descriptor, syntaxToken.GetLocation(), messageArgs));
		}

		/// <summary>
		///     Emits a diagnostic for <paramref name="syntaxNode" /> using the <paramref name="messageArgs" /> to format the
		///     diagnostic message.
		/// </summary>
		/// <param name="context">The context in which the diagnostic should be emitted.</param>
		/// <param name="syntaxNode">The syntax node the diagnostic is emitted for.</param>
		/// <param name="messageArgs">The arguments for formatting the diagnostic message.</param>
		protected void EmitDiagnostic(SemanticModelAnalysisContext context, [NotNull] SyntaxNode syntaxNode, params object[] messageArgs)
		{
			context.ReportDiagnostic(Diagnostic.Create(Descriptor, syntaxNode.GetLocation(), messageArgs));
		}

		/// <summary>
		///     Emits a diagnostic for <paramref name="syntaxToken" /> using the <paramref name="messageArgs" /> to format the
		///     diagnostic message.
		/// </summary>
		/// <param name="context">The context in which the diagnostic should be emitted.</param>
		/// <param name="syntaxToken">The syntax token the diagnostic is emitted for.</param>
		/// <param name="messageArgs">The arguments for formatting the diagnostic message.</param>
		protected void EmitDiagnostic(SemanticModelAnalysisContext context, SyntaxToken syntaxToken, params object[] messageArgs)
		{
			context.ReportDiagnostic(Diagnostic.Create(Descriptor, syntaxToken.GetLocation(), messageArgs));
		}

		/// <summary>
		///     Emits a diagnostic for <paramref name="symbol" /> using the <paramref name="messageArgs" /> to format the diagnostic
		///     message.
		/// </summary>
		/// <param name="context">The context in which the diagnostic should be emitted.</param>
		/// <param name="symbol">The symbol the diagnostic is emitted for.</param>
		/// <param name="messageArgs">The arguments for formatting the diagnostic message.</param>
		protected void EmitDiagnostic(SymbolAnalysisContext context, [NotNull] ISymbol symbol, params object[] messageArgs)
		{
			context.ReportDiagnostic(Diagnostic.Create(Descriptor, symbol.Locations[0], messageArgs));
		}
	}
}