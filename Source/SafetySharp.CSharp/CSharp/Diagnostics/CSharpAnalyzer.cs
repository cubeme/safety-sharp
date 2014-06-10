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
	using System.Collections.Generic;
	using System.Collections.Immutable;
	using System.Linq;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Utilities;

	/// <summary>
	///     A base class for C# code analyzers.
	/// </summary>
	public abstract class CSharpAnalyzer : IDiagnosticAnalyzer
	{
		/// <summary>
		///     Gets the descriptor for the diagnostic emitted by the analyzer.
		/// </summary>
		protected DiagnosticDescriptor Descriptor { get; private set; }

		/// <summary>
		///     Returns a set of descriptors for the diagnostics that this analyzer is capable of producing.
		/// </summary>
		public ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics { get; private set; }

		/// <summary>
		///     Gets all C# code analyzers defined by Safety Sharp.
		/// </summary>
		public static IEnumerable<CSharpAnalyzer> GetAnalyzers()
		{
			return typeof(CSharpAnalyzer)
				.Assembly
				.GetTypes()
				.Where(t => t.IsClass && !t.IsAbstract && typeof(CSharpAnalyzer).IsAssignableFrom(t))
				.Select(Activator.CreateInstance)
				.Cast<CSharpAnalyzer>();
		}

		/// <summary>
		///     Describes the error diagnostic of the analyzer.
		/// </summary>
		/// <param name="identifier">The identifier of the analyzer's diagnostic.</param>
		/// <param name="description">The description of the diagnostic.</param>
		/// <param name="messageFormat">The message format of the diagnostic.</param>
		protected void Error(string identifier, string description, string messageFormat)
		{
			SetDescriptor(identifier, description, messageFormat, DiagnosticSeverity.Error);
		}

		/// <summary>
		///     Describes the error diagnostic of the analyzer.
		/// </summary>
		/// <param name="identifier">The identifier of the analyzer's diagnostic.</param>
		/// <param name="description">The description of the diagnostic.</param>
		/// <param name="messageFormat">The message format of the diagnostic.</param>
		protected void Warning(string identifier, string description, string messageFormat)
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
		private void SetDescriptor(string identifier, string description, string messageFormat, DiagnosticSeverity severity)
		{
			Assert.That(Descriptor == null, "A descriptor has already been set.");
			Requires.NotNullOrWhitespace(identifier, () => identifier);
			Requires.NotNullOrWhitespace(description, () => description);
			Requires.NotNullOrWhitespace(messageFormat, () => messageFormat);
			Requires.InRange(severity, () => severity);
			Requires.ArgumentSatisfies(identifier.StartsWith(Compiler.DiagnosticsPrefix), () => identifier,
							   "Diagnostic identifier does not start with prefix '{0}'.", Compiler.DiagnosticsPrefix);

			Descriptor = new DiagnosticDescriptor(identifier, description, messageFormat, Compiler.DiagnosticsCategory, severity, true);
			SupportedDiagnostics = ImmutableArray.Create(Descriptor);
		}
	}
}