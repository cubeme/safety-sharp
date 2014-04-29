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

namespace SafetySharp.CSharp
{
	using System;
	using System.Collections.Immutable;
	using System.Threading;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Diagnostics;

	[DiagnosticAnalyzer]
	[ExportDiagnosticAnalyzer(DiagnosticId, LanguageNames.CSharp)]
	public class TestAnalyzer : ISyntaxNodeAnalyzer<SyntaxKind>
	{
		internal const string DiagnosticId = "MakeConst";
		internal const string Description = "Make Constant";
		internal const string MessageFormat = "Local vars are unsupported! {0}";
		internal const string Category = "Usage";

		internal static DiagnosticDescriptor Rule = new
			DiagnosticDescriptor(DiagnosticId, Description, MessageFormat, Category,
								 DiagnosticSeverity.Error);

		public ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics
		{
			get { return ImmutableArray.Create(Rule); }
		}

		public ImmutableArray<SyntaxKind> SyntaxKindsOfInterest
		{
			get { return ImmutableArray.Create(SyntaxKind.LocalDeclarationStatement); }
		}

		public void AnalyzeNode(SyntaxNode node, SemanticModel semanticModel,
								Action<Diagnostic> addDiagnostic, CancellationToken cancellationToken)
		{
			addDiagnostic(Diagnostic.Create(Rule, node.GetLocation(), "Depp!"));
		}
	}
}