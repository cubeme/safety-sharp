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
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Modeling;
	using Roslyn;
	using Roslyn.Symbols;

	/// <summary>
	///     Ensures that a method or property marked with the <see cref="ProvidedAttribute" /> is not <c>extern</c>.
	/// </summary>
	[DiagnosticAnalyzer(LanguageNames.CSharp), UsedImplicitly]
	public sealed class PortKindAnalyzer : Analyzer
	{
		/// <summary>
		///     The error diagnostic emitted by the analyzer when the update method is extern.
		/// </summary>
		private static readonly DiagnosticInfo ExternUpdateMethod = DiagnosticInfo.Error(
			DiagnosticIdentifier.ExternUpdateMethod,
			"A component's Update method cannot be extern.",
			String.Format("'{{0}}' cannot be extern as it overrides '{0}.Update()'.", typeof(Component).FullName));

		/// <summary>
		///     The error diagnostic emitted by the analyzer when a provided port is extern.
		/// </summary>
		private static readonly DiagnosticInfo ExternProvidedPort = DiagnosticInfo.Error(
			DiagnosticIdentifier.ExternProvidedPort,
			String.Format("A method or property marked with '{0}' cannot be extern.", typeof(ProvidedAttribute).FullName),
			"Provided port '{0}' cannot be extern.");

		/// <summary>
		///     The error diagnostic emitted by the analyzer when a required port is not extern.
		/// </summary>
		private static readonly DiagnosticInfo NonExternRequiredPort = DiagnosticInfo.Error(
			DiagnosticIdentifier.NonExternRequiredPort,
			String.Format("A method or property marked with '{0}' must be extern.", typeof(RequiredAttribute).FullName),
			"Required port '{0}' must be extern.");

		/// <summary>
		///     The error diagnostic emitted by the analyzer when the update method is marked as a port.
		/// </summary>
		private static readonly DiagnosticInfo UpdateMethodMarkedAsPort = DiagnosticInfo.Error(
			DiagnosticIdentifier.UpdateMethodMarkedAsPort,
			String.Format("A component's Update method cannot be marked with '{0}' or '{1}'.",
				typeof(ProvidedAttribute).FullName,
				typeof(RequiredAttribute).FullName),
			String.Format("'{{0}}' overrides '{0}.Update()' and is therefore not a port. The method cannot be marked with '{1}' or '{2}'.",
				typeof(Component).FullName,
				typeof(ProvidedAttribute).FullName,
				typeof(RequiredAttribute).FullName));

		/// <summary>
		///     The error diagnostic emitted by the analyzer if a method or property is marked as both required and provided.
		/// </summary>
		private static readonly DiagnosticInfo AmbiguousPortKind = DiagnosticInfo.Error(
			DiagnosticIdentifier.AmbiguousPortKind,
			String.Format("A method or property cannot be marked with both '{0}' and '{1}'.",
				typeof(RequiredAttribute).FullName,
				typeof(ProvidedAttribute).FullName),
			String.Format("'{{0}}' cannot be marked with both '{0}' and '{1}'.",
				typeof(RequiredAttribute).FullName,
				typeof(ProvidedAttribute).FullName));

		/// <summary>
		///     The error diagnostic emitted by the analyzer when a property accessor is marked as either required or provided.
		/// </summary>
		private static readonly DiagnosticInfo PortPropertyAccessor = DiagnosticInfo.Error(
			DiagnosticIdentifier.PortPropertyAccessor,
			String.Format("Property getters and setters cannot be marked with either '{0}' or '{1}'.",
				typeof(RequiredAttribute).FullName,
				typeof(ProvidedAttribute).FullName),
			String.Format("'{{0}}' cannot be marked with either '{0}' or '{1}'.",
				typeof(RequiredAttribute).FullName,
				typeof(ProvidedAttribute).FullName));

		/// <summary>
		///     The error diagnostic emitted by the analyzer when an interface method or property is unmarked.
		/// </summary>
		private static readonly DiagnosticInfo UnmarkedInterfacePort = DiagnosticInfo.Error(
			DiagnosticIdentifier.UnmarkedInterfacePort,
			String.Format("A method or property within a component interface must be marked with either '{0}' or '{1}'.",
				typeof(RequiredAttribute).FullName,
				typeof(ProvidedAttribute).FullName),
			String.Format("'{{0}}' must be marked with either '{0}' or '{1}'.",
				typeof(RequiredAttribute).FullName,
				typeof(ProvidedAttribute).FullName));

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public PortKindAnalyzer()
			: base(ExternProvidedPort, NonExternRequiredPort, AmbiguousPortKind, UpdateMethodMarkedAsPort,
				ExternUpdateMethod, PortPropertyAccessor, UnmarkedInterfacePort)
		{
		}

		/// <summary>
		///     Called once at session start to register actions in the analysis context.
		/// </summary>
		/// <param name="context">The analysis context that should be used to register analysis actions.</param>
		public override void Initialize(AnalysisContext context)
		{
			context.RegisterSymbolAction(Analyze, SymbolKind.Method, SymbolKind.Property);
		}

		/// <summary>
		///     Performs the analysis.
		/// </summary>
		/// <param name="context">The context in which the analysis should be performed.</param>
		private static void Analyze(SymbolAnalysisContext context)
		{
			var compilation = context.Compilation;
			var symbol = context.Symbol;

			if (!symbol.ContainingType.ImplementsIComponent(compilation))
				return;

			var methodSymbol = symbol as IMethodSymbol;
			var hasRequiredAttribute = symbol.HasAttribute<RequiredAttribute>(compilation);
			var hasProvidedAttribute = symbol.HasAttribute<ProvidedAttribute>(compilation);

			var isAccessor = methodSymbol != null && methodSymbol.AssociatedSymbol is IPropertySymbol;
			if (isAccessor)
			{
				if (hasProvidedAttribute || hasRequiredAttribute)
					PortPropertyAccessor.Emit(context, symbol, symbol.ToDisplayString());
				return;
			}

			if (methodSymbol != null && methodSymbol.Overrides(compilation.GetUpdateMethodSymbol()))
			{
				if (hasRequiredAttribute || hasProvidedAttribute)
					UpdateMethodMarkedAsPort.Emit(context, symbol, symbol.ToDisplayString());
				else if (methodSymbol.IsExtern)
					ExternUpdateMethod.Emit(context, symbol, symbol.ToDisplayString());

				return;
			}

			if (hasRequiredAttribute && hasProvidedAttribute)
			{
				AmbiguousPortKind.Emit(context, symbol, symbol.ToDisplayString());
				return;
			}

			if (symbol.ContainingType.TypeKind == TypeKind.Interface)
			{
				if (!hasRequiredAttribute && !hasProvidedAttribute)
					UnmarkedInterfacePort.Emit(context, symbol, symbol.ToDisplayString());
			}
			else
			{
				if (hasProvidedAttribute && symbol.IsExtern)
					ExternProvidedPort.Emit(context, symbol, symbol.ToDisplayString());
				else if (hasRequiredAttribute && !symbol.IsExtern)
					NonExternRequiredPort.Emit(context, symbol, symbol.ToDisplayString());
			}
		}
	}
}