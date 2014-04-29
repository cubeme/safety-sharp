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
	using System.Collections.Immutable;
	using Microsoft.CodeAnalysis;
	using Utilities;

	/// <summary>
	///     A base class for C# code analyzers.
	/// </summary>
	public abstract class CSharpAnalyzer
	{
		/// <summary>
		///     The prefix that is used for all diagnostic identifiers.
		/// </summary>
		protected const string IdentifierPrefix = "SS";

		/// <summary>
		///     The category that is used for all diagnostics.
		/// </summary>
		private const string Category = "Safety Sharp";

		/// <summary>
		///     Gets the descriptor for the diagnostic emitted by the analyzer.
		/// </summary>
		protected DiagnosticDescriptor Descriptor { get; private set; }

		/// <summary>
		///     Returns a set of descriptors for the diagnostics that this analyzer is capable of producing.
		/// </summary>
		public ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics { get; private set; }

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
		/// <param name="severity">The severity of the diagnostic.</param>
		protected void Warning(string identifier, string description, string messageFormat, DiagnosticSeverity severity)
		{
			SetDescriptor(identifier, description, messageFormat, severity);
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
			Assert.ArgumentNotNullOrWhitespace(identifier, () => identifier);
			Assert.ArgumentNotNullOrWhitespace(description, () => description);
			Assert.ArgumentNotNullOrWhitespace(messageFormat, () => messageFormat);
			Assert.ArgumentInRange(severity, () => severity);
			Assert.That(Descriptor == null, "A descriptor has already been set.");

			Descriptor = new DiagnosticDescriptor(IdentifierPrefix + identifier, description, messageFormat, Category, severity);
			SupportedDiagnostics = ImmutableArray.Create(Descriptor);
		}
	}
}