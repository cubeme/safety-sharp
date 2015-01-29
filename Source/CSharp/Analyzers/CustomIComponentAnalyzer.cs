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

namespace SafetySharp.CSharp.Analyzers
{
	using System;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Modeling;
	using Roslyn;
	using Roslyn.Symbols;

	/// <summary>
	///     Ensures that no class implements <see cref="IComponent" /> without being derived from <see cref="Component" />.
	/// </summary>
	[DiagnosticAnalyzer]
	public class CustomIComponentAnalyzer : CSharpAnalyzer
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public CustomIComponentAnalyzer()
		{
			Error(1009,
				String.Format("A class cannot implement '{0}' when it is not derived from '{1}'.",
					typeof(IComponent).FullName,
					typeof(Component).FullName),
				String.Format("Class '{{0}}' cannot implement '{0}' explicitly; derive from '{1}' instead.",
					typeof(IComponent).FullName,
					typeof(Component).FullName));
		}

		/// <summary>
		///     Called once at session start to register actions in the analysis context.
		/// </summary>
		/// <param name="context" />
		public override void Initialize(AnalysisContext context)
		{
			context.RegisterSymbolAction(Analyze, SymbolKind.NamedType);
		}

		/// <summary>
		///     Performs the analysis.
		/// </summary>
		/// <param name="context">The context in which the analysis should be performed.</param>
		private void Analyze(SymbolAnalysisContext context)
		{
			var compilation = context.Compilation;
			var symbol = context.Symbol as ITypeSymbol;

			if (symbol == null || symbol.TypeKind != TypeKind.Class)
				return;

			if (symbol.ImplementsIComponent(compilation) && !symbol.IsDerivedFromComponent(compilation))
				EmitDiagnostic(context, symbol, symbol.ToDisplayString());
		}
	}
}