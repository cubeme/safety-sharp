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
	using System.Threading;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Diagnostics;

	/// <summary>
	///     Ensures that no enumeration members explicitly declare a constant value.
	/// </summary>
	[DiagnosticAnalyzer]
	[ExportDiagnosticAnalyzer(DiagnosticIdentifier, LanguageNames.CSharp)]
	public class EnumMemberAnalyzer : SyntaxNodeAnalyzer<EnumMemberDeclarationSyntax>
	{
		private const string DiagnosticIdentifier = IdentifierPrefix + "1002";

		/// <summary>
		///     Initializes a new instance of the <see cref="EnumMemberAnalyzer" /> type.
		/// </summary>
		public EnumMemberAnalyzer()
		{
			Error(DiagnosticIdentifier,
				  "Values of enumeration members must not be explicitly declared.",
				  "Value of enum member '{0}' cannot be declared explicitly.");
		}

		/// <summary>
		///     Analyzes a syntax node.
		/// </summary>
		/// <param name="node">The syntax node that should be analyzed.</param>
		/// <param name="addDiagnostic">A delegate that should be used to emit diagnostics.</param>
		/// <param name="cancellationToken">A token that should be checked for cancelling the analysis.</param>
		protected override void Analyze(EnumMemberDeclarationSyntax node, DiagnosticCallback addDiagnostic, CancellationToken cancellationToken)
		{
			if (node.EqualsValue != null)
				addDiagnostic(node.EqualsValue.Value, node.Identifier.ValueText);
		}
	}
}