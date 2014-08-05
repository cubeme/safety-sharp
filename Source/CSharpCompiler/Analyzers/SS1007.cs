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
	[ExportDiagnosticAnalyzer(Identifier, LanguageNames.CSharp)]
	public class SS1007 : SemanticModelAnalyzer
	{
		/// <summary>
		///     The identifier of the diagnostic emitted by the analyzer.
		/// </summary>
		private const string Identifier = Prefix + "1007";

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public SS1007()
		{
			Error(Identifier,
				  "Enumeration declarations must not explicitly declare an underlying type.",
				  "Enum '{0}' must not explicitly declare an underlying type.");
		}

		/// <summary>
		///     Analyzes the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model that should be analyzed.</param>
		protected override void Analyze(SemanticModel semanticModel)
		{
			var enumDeclarations = semanticModel
				.SyntaxTree.Descendants<EnumDeclarationSyntax>()
				.Where(enumDeclatation => enumDeclatation.BaseList != null);

			foreach (var enumDeclaration in enumDeclarations)
				EmitDiagnostic(enumDeclaration.BaseList.Types.First(), semanticModel.GetDeclaredSymbol(enumDeclaration).ToDisplayString());
		}
	}
}