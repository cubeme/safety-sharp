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
	using Microsoft.CodeAnalysis.Diagnostics;
	using Modeling;
	using Roslyn;
	using Roslyn.Symbols;

	/// <summary>
	///     Ensures that the port type of an interface implementing method or property matches the port type of the
	///     corresponding interface method or property.
	/// </summary>
	[DiagnosticAnalyzer]
	[ExportDiagnosticAnalyzer(Identifier, LanguageNames.CSharp)]
	public class SS1005 : SymbolAnalyzer<INamedTypeSymbol>
	{
		/// <summary>
		///     The identifier of the diagnostic emitted by the analyzer.
		/// </summary>
		private const string Identifier = Prefix + "1005";

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public SS1005()
			: base(SymbolKind.NamedType)
		{
			Error(Identifier,
				  "Method or property does not implement the corresponding interface method or property, as the port types are different.",
				  "'{0}' does not implement interface member '{1}'. '{1}' is declared as a {2} port, but is implemented as a {3} port.");
		}

		/// <summary>
		///     Analyzes the <paramref name="symbol" />.
		/// </summary>
		/// <param name="symbol">The symbol that should be analyzed.</param>
		/// <param name="compilation">The compilation the symbol is declared in.</param>
		protected override void Analyze(INamedTypeSymbol symbol, Compilation compilation)
		{
			if (symbol.TypeKind != TypeKind.Class || !symbol.IsDerivedFromComponent(compilation))
				return;

			foreach (var interfaceSymbol in symbol.AllInterfaces.Where(interfaceSymbol => interfaceSymbol.ImplementsIComponent(compilation)))
			{
				foreach (var interfaceMember in interfaceSymbol.GetMembers())
				{
					var implementingMember = symbol.FindImplementationForInterfaceMember(interfaceMember);
					if (!Equals(implementingMember.ContainingSymbol, symbol))
						continue;

					var interfaceIsRequired = interfaceMember.HasAttribute<RequiredAttribute>(compilation);
					var interfaceIsProvided = interfaceMember.HasAttribute<ProvidedAttribute>(compilation);

					var implementationIsRequired = implementingMember.HasAttribute<RequiredAttribute>(compilation) || implementingMember.IsExtern;
					var implementationIsProvided = implementingMember.HasAttribute<ProvidedAttribute>(compilation) || !implementingMember.IsExtern;

					// If we can't uniquely classify the port type of either the interface member or the implementation, 
					// there is another problem that another analyzer deals with. So let's just ignore it here.
					if ((interfaceIsRequired && interfaceIsProvided) || (implementationIsProvided && implementationIsRequired))
						continue;

					if (interfaceIsRequired && !implementationIsRequired)
						EmitDiagnostic(implementingMember, implementingMember.ToDisplayString(), interfaceMember.ToDisplayString(),
									   "required", "provided");

					if (interfaceIsProvided && !implementationIsProvided)
						EmitDiagnostic(implementingMember, implementingMember.ToDisplayString(), interfaceMember.ToDisplayString(),
									   "provided", "required");
				}
			}
		}
	}
}