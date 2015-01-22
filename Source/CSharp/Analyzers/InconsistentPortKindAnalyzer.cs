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
	using System.Linq;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Modeling;
	using Roslyn;
	using Roslyn.Symbols;

	/// <summary>
	///     Ensures that the port kind of an interface implementing method or property matches the port kind of the
	///     corresponding interface method or property.
	/// </summary>
	[DiagnosticAnalyzer]
	public class InconsistentPortKindAnalyzer : CSharpAnalyzer
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public InconsistentPortKindAnalyzer()
		{
			Error(1005,
				"Method or property does not implement the corresponding interface method or property, as the port kinds are different.",
				"'{0}' does not implement interface member '{1}'. '{1}' is declared as a {2} port, but is implemented as a {3} port.");
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
		private void Analyze(SymbolAnalysisContext context)
		{
			var compilation = context.Compilation;
			var symbol = (INamedTypeSymbol)context.Symbol;

			if (symbol.TypeKind != TypeKind.Class || !symbol.IsDerivedFromComponent(compilation))
				return;

			var interfaceMembers = symbol
				.AllInterfaces
				.Where(interfaceSymbol => interfaceSymbol.ImplementsIComponent(compilation))
				.SelectMany(interfaceSymbol => interfaceSymbol.GetMembers());

			foreach (var interfaceMember in interfaceMembers)
				CheckMember(context, symbol, compilation, interfaceMember);
		}

		/// <summary>
		///     Checks whether the <paramref name="symbol" />'s implementing member for <paramref name="interfaceMember" /> has the
		///     correct port kind.
		/// </summary>
		/// <param name="context">The context in which the analysis should be performed.</param>
		/// <param name="symbol">The symbol that should be analyzed.</param>
		/// <param name="compilation">The compilation the symbol is declared in.</param>
		/// <param name="interfaceMember">The interface member that should be checked.</param>
		private void CheckMember(SymbolAnalysisContext context, ITypeSymbol symbol, Compilation compilation, ISymbol interfaceMember)
		{
			var implementingMember = symbol.FindImplementationForInterfaceMember(interfaceMember);

			var interfaceIsRequired = interfaceMember.HasAttribute<RequiredAttribute>(compilation);
			var interfaceIsProvided = interfaceMember.HasAttribute<ProvidedAttribute>(compilation);

			var implementationIsRequired = implementingMember.HasAttribute<RequiredAttribute>(compilation) || implementingMember.IsExtern;
			var implementationIsProvided = implementingMember.HasAttribute<ProvidedAttribute>(compilation) || !implementingMember.IsExtern;

			// If we can't uniquely classify the port kind of either the interface member or the implementation, 
			// there is another problem that another analyzer deals with. So let's just ignore it here.
			if ((interfaceIsRequired && interfaceIsProvided) || (implementationIsProvided && implementationIsRequired))
				return;

			if (interfaceIsRequired && !implementationIsRequired)
				EmitDiagnostic(context, implementingMember, implementingMember.ToDisplayString(), interfaceMember.ToDisplayString(),
					"required", "provided");

			if (interfaceIsProvided && !implementationIsProvided)
				EmitDiagnostic(context, implementingMember, implementingMember.ToDisplayString(), interfaceMember.ToDisplayString(),
					"provided", "required");
		}
	}
}