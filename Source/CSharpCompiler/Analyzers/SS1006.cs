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
	using System.Linq;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Roslyn;
	using Roslyn.Syntax;

	/// <summary>
	///     Ensures that no enumeration members explicitly declare a constant value.
	/// </summary>
	[DiagnosticAnalyzer]
	[ExportDiagnosticAnalyzer("", LanguageNames.CSharp)]
	public class SS1006 : SemanticModelAnalyzer
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public SS1006()
		{
			Error(1006,
				"Values of enumeration members must not be explicitly declared.",
				"Value of enum member '{0}' cannot be declared explicitly.");
		}

		/// <summary>
		///     Analyzes the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model that should be analyzed.</param>
		protected override void Analyze(SemanticModel semanticModel)
		{
			var enumDeclarations = semanticModel
				.SyntaxTree.Descendants<EnumMemberDeclarationSyntax>()
				.Where(enumMember => enumMember.EqualsValue != null);

			foreach (var enumMember in enumDeclarations)
				EmitDiagnostic(enumMember.EqualsValue.Value, semanticModel.GetDeclaredSymbol(enumMember).ToDisplayString());
		}
	}
}