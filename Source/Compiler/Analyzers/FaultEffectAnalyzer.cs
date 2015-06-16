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
	using Microsoft.CodeAnalysis.Diagnostics;
	using Roslyn;
	using Roslyn.Symbols;

	/// <summary>
	///     Ensures that fault effects are declared correctly.
	/// </summary>
	[DiagnosticAnalyzer(LanguageNames.CSharp), UsedImplicitly]
	public sealed class FaultEffectAnalyzer : Analyzer
	{
		/// <summary>
		///     Indicates that the fault effect overrides an unknown method.
		/// </summary>
		private static readonly DiagnosticInfo _unknownMethod = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectUnknownMethod,
			"Fault effects must override existing methods of the affected component.",
			"Invalid fault effect '{0}': Affected component of type '{1}' does not declare a signature-compatible method named '{2}'.");

		/// <summary>
		///     Indicates that the fault effect overrides an unknown property.
		/// </summary>
		private static readonly DiagnosticInfo _unknownProperty = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectUnknownProperty,
			"Fault effects must override existing property accessors of the affected component.",
			"Invalid fault effect '{0}': Affected component of type '{1}' does not declare a {4} for a property with name '{2}' of type '{3}'.");

		/// <summary>
		///     Indicates that the member the fault effect overrides is ambiguous.
		/// </summary>
		private static readonly DiagnosticInfo _ambiguousMember = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectAmbiguousMember,
			"The fault effect's affected member is ambiguous.",
			"Invalid fault effect '{0}': Affected member is ambiguous; could be {1}.");

		/// <summary>
		///     Indicates that the fault effect overrides a member of a base class.
		/// </summary>
		private static readonly DiagnosticInfo _baseMember = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectBaseMember,
			"Fault effects can only override members declared by the affected component.",
			"Fault effect '{0}' cannot affect inherited member '{1}'.");

		/// <summary>
		///     Indicates that the fault effect declares an optional parameter.
		/// </summary>
		private static readonly DiagnosticInfo _optionalParameter = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectOptionalParameter,
			"Fault effects cannot declare optional parameters.",
			"Invalid optional parameter '{0}' declared by fault effect '{1}'.");

		/// <summary>
		///     Indicates that the fault declares no effects.
		/// </summary>
		private static readonly DiagnosticInfo _noEffects = DiagnosticInfo.Warning(
			DiagnosticIdentifier.FaultWithoutEffects,
			"The fault does not declare any fault effects.",
			"Fault '{0}' does not declare any fault effects.");

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public FaultEffectAnalyzer()
			: base(_unknownMethod, _unknownProperty, _baseMember, _optionalParameter, _noEffects, _ambiguousMember)
		{
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
		private static void Analyze(SymbolAnalysisContext context)
		{
			var faultSymbol = context.Symbol as ITypeSymbol;
			if (faultSymbol == null || !faultSymbol.IsDerivedFromFault(context.Compilation))
				return;

			var componentSymbol = faultSymbol.ContainingType;
			if (componentSymbol == null || !componentSymbol.IsDerivedFromComponent(context.Compilation))
				return;

			var faultMethods = faultSymbol
				.GetMembers()
				.OfType<IMethodSymbol>()
				.Where(candidate => !candidate.IsUpdateMethod(context.Compilation))
				.Where(candidate =>
					candidate.MethodKind == MethodKind.Ordinary ||
					candidate.MethodKind == MethodKind.PropertyGet ||
					candidate.MethodKind == MethodKind.PropertySet)
				.ToArray();

			if (faultMethods.Length == 0)
				_noEffects.Emit(context, faultSymbol, faultSymbol.ToDisplayString());

			foreach (var method in faultMethods)
			{
				var optionalParameter = method.Parameters.FirstOrDefault(parameter => parameter.IsOptional);
				if (optionalParameter != null)
					_optionalParameter.Emit(context, optionalParameter, optionalParameter.Name, method.ToDisplayString());

				var candidateMethods = method.GetAffectedMethodCandidates(componentSymbol);
				if (candidateMethods.Length == 0)
				{
					// There is no port with a matching name; there might be two reasons:
					// - The affected component doesn't declare a signature-compatible method with the given name
					// - The component inherited, but did not redeclare or override a port with the given name
					// Even though a generic "port not found" message is enough for both cases, we improve the
					// diagnosis by giving the user more context

					var baseType = componentSymbol.BaseType;
					IMethodSymbol[] baseCandidateMethods = null;

					while (baseType != null && (baseCandidateMethods == null || baseCandidateMethods.Length > 1))
					{
						baseCandidateMethods = baseType
							.GetMembers(method.Name)
							.OfType<IMethodSymbol>()
							.Where(candidate => componentSymbol.CanAccessBaseMember(candidate))
							.ToArray();

						baseType = baseType.BaseType;
					}

					if (baseCandidateMethods != null && baseCandidateMethods.Length > 0)
						_baseMember.Emit(context, method, method.ToDisplayString(), baseCandidateMethods[0].ToDisplayString());
					else
					{
						if (method.IsPropertyAccessor())
						{
							var property = method.GetPropertySymbol();
							_unknownProperty.Emit(context, property, property.ToDisplayString(), componentSymbol.ToDisplayString(),
								property.Name, property.Type.ToDisplayString(), method.MethodKind == MethodKind.PropertyGet ? "getter" : "setter");
						}
						else
							_unknownMethod.Emit(context, method, method.ToDisplayString(), componentSymbol.ToDisplayString(), method.Name);
					}
				}
				else if (candidateMethods.Length > 1)
				{
					_ambiguousMember.Emit(context, method, method.ToDisplayString(),
						String.Join(", ", candidateMethods.Select(m => String.Format("'{0}'", m.ToDisplayString()))));
				}
			}
		}
	}
}