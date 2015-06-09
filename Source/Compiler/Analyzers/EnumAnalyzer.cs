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
	using System.Linq;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Roslyn;
	using Roslyn.Syntax;

	/// <summary>
	///     Ensures that no enumeration members explicitly declare a constant value and that the underlying type of all enumerations
	///     is <see cref="int" />.
	/// </summary>
	[DiagnosticAnalyzer(LanguageNames.CSharp), UsedImplicitly]
	public sealed class EnumAnalyzer : Analyzer
	{
		/// <summary>
		///     The error diagnostic emitted by the analyzer.
		/// </summary>
		private static readonly DiagnosticInfo ExplicitEnumType = DiagnosticInfo.Error(
			DiagnosticIdentifier.ExplicitEnumType,
			"Enumeration declarations must not explicitly declare an underlying type.",
			"Enum '{0}' must not explicitly declare an underlying type.");

		/// <summary>
		///     The error diagnostic emitted by the analyzer.
		/// </summary>
		private static readonly DiagnosticInfo ExplicitEnumMemberValue = DiagnosticInfo.Error(
			DiagnosticIdentifier.ExplicitEnumMemberValue,
			"Values of enumeration members must not be explicitly declared.",
			"Value of enum member '{0}' cannot be declared explicitly.");

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public EnumAnalyzer()
			: base(ExplicitEnumType, ExplicitEnumMemberValue)
		{
		}

		/// <summary>
		///     Called once at session start to register actions in the analysis context.
		/// </summary>
		/// <param name="context">The analysis context that should be used to register analysis actions.</param>
		public override void Initialize(AnalysisContext context)
		{
			context.RegisterSemanticModelAction(Analyze);
		}

		/// <summary>
		///     Performs the analysis.
		/// </summary>
		/// <param name="context">The context in which the analysis should be performed.</param>
		private static void Analyze(SemanticModelAnalysisContext context)
		{
			var enumDeclarations = context
				.SemanticModel
				.SyntaxTree.Descendants<EnumDeclarationSyntax>();

			foreach (var enumDeclaration in enumDeclarations)
			{
				if (enumDeclaration.BaseList != null)
				{
					ExplicitEnumType.Emit(context, enumDeclaration.BaseList.Types.First(),
						context.SemanticModel.GetDeclaredSymbol(enumDeclaration).ToDisplayString());
				}

				var enumMembers = enumDeclaration
					.Descendants<EnumMemberDeclarationSyntax>()
					.Where(enumMember => enumMember.EqualsValue != null);

				foreach (var enumMember in enumMembers)
				{
					ExplicitEnumMemberValue.Emit(context, enumMember.EqualsValue.Value,
						context.SemanticModel.GetDeclaredSymbol(enumMember).ToDisplayString());
				}
			}
		}
	}
}