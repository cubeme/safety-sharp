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
		///     Indicates that the fault effect overrides an unknown method port.
		/// </summary>
		private static readonly DiagnosticInfo _unknownMethodPort = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectUnknownMethod,
			"Fault effects must override existing methods of the affected component.",
			"Invalid fault effect '{0}': Affected component of type '{1}' does not declare a method named '{2}'.");

		/// <summary>
		///     Indicates that the fault effect overrides an unknown property port.
		/// </summary>
		private static readonly DiagnosticInfo _unknownPropertyPort = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectUnknownProperty,
			"Fault effects must override existing property of the affected component.",
			"Invalid fault effect '{0}': Affected component of type '{1}' does not declare a property named '{2}' with the corresponding accessors.");

		/// <summary>
		///     Indicates that the member the fault effect overrides is ambiguous.
		/// </summary>
		private static readonly DiagnosticInfo _ambiguousMember = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectAmbiguousMember,
			"The fault effect's affected member is ambiguous.",
			"Invalid fault effect '{0}': Affected member is ambiguous; could be {1}.");

		/// <summary>
		///     Indicates that the fault effect overrides an unknown port.
		/// </summary>
		private static readonly DiagnosticInfo _signatureIncompatible = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectSignatureIncompatible,
			"Fault effects must be signature compatible with the overriden port of the affected component.",
			"Fault effect '{0}' is not signature compatible with '{1}' or any of its overloads.");

		/// <summary>
		///     Indicates that the fault effect overrides a property port of a different type.
		/// </summary>
		private static readonly DiagnosticInfo _typeIncompatible = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectIncompatibleType,
			"Fault effect properties must be declared with the type of the overriden property port of the affected component.",
			"Fault effect '{0}' must be a property of type '{1}'.");

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
			: base(
				_unknownMethodPort, _unknownPropertyPort, _signatureIncompatible, _baseMember, _optionalParameter,
				_typeIncompatible, _noEffects, _ambiguousMember)
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

			var faultProperties = faultSymbol.GetMembers().OfType<IPropertySymbol>().ToArray();
			var faultMethods = faultSymbol
				.GetMembers()
				.OfType<IMethodSymbol>()
				.Where(candidate => candidate.MethodKind == MethodKind.Ordinary && !candidate.IsUpdateMethod(context.Compilation))
				.ToArray();

			if (faultMethods.Length == 0 && faultProperties.Length == 0)
				_noEffects.Emit(context, faultSymbol, faultSymbol.ToDisplayString());

			foreach (var method in faultMethods)
			{
				var optionalParameter = method.Parameters.FirstOrDefault(parameter => parameter.IsOptional);
				if (optionalParameter != null)
					_optionalParameter.Emit(context, optionalParameter, optionalParameter.Name, method.ToDisplayString());

				var candidateMethods = componentSymbol
					.GetMembers()
					.OfType<IMethodSymbol>()
					.Where(candidate => candidate.MethodKind == MethodKind.Ordinary || candidate.MethodKind == MethodKind.ExplicitInterfaceImplementation)
					.Where(candidate => candidate.MethodKind == MethodKind.ExplicitInterfaceImplementation
						? candidate.ExplicitInterfaceImplementations[0].Name == method.Name
						: candidate.Name == method.Name)
					.ToArray();

				if (candidateMethods.Length == 0)
				{
					// There is no port with a matching name; there might be two reasons:
					// - The affected component doesn't declare a port with the given name
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
						_unknownMethodPort.Emit(context, method, method.ToDisplayString(), componentSymbol.ToDisplayString(), method.Name);
				}
				else
				{
					var signatureCompatibleMethods = candidateMethods.Where(candidate => candidate.IsSignatureCompatibleTo(method)).ToArray();

					if (signatureCompatibleMethods.Length > 1)
					{
						_ambiguousMember.Emit(context, method, method.ToDisplayString(),
							String.Join(", ", candidateMethods.Select(m => String.Format("'{0}'", m.ToDisplayString()))));
					}
					else if (signatureCompatibleMethods.Length == 0)
						_signatureIncompatible.Emit(context, method, method.ToDisplayString(), candidateMethods[0].ToDisplayString());
				}
			}

			foreach (var property in faultProperties)
			{
				var candidateProperties = componentSymbol
					.GetMembers()
					.OfType<IPropertySymbol>()
					.Where(candidate => candidate.ExplicitInterfaceImplementations.Length != 0
						? candidate.ExplicitInterfaceImplementations[0].Name == property.Name
						: candidate.Name == property.Name)
					.ToArray();

				if (candidateProperties.Length == 0)
				{
					// There is no port with a matching name; there might be two reasons:
					// - The affected component doesn't declare a port with the given name
					// - The component inherited, but did not redeclare or override a port with the given name
					// Even though a generic "port not found" message is enough for both cases, we improve the
					// diagnosis by giving the user more context

					var baseType = componentSymbol.BaseType;
					IPropertySymbol baseProperty = null;

					while (baseType != null && baseProperty == null)
					{
						baseProperty = baseType
							.GetMembers(property.Name)
							.OfType<IPropertySymbol>()
							.FirstOrDefault(candidate => componentSymbol.CanAccessBaseMember(candidate));

						baseType = baseType.BaseType;
					}

					if (baseProperty != null)
						_baseMember.Emit(context, property, property.ToDisplayString(), baseProperty.ToDisplayString());
					else
						_unknownPropertyPort.Emit(context, property, property.ToDisplayString(), componentSymbol.ToDisplayString(), property.Name);
				}
				else if (candidateProperties.Length > 1)
				{
					_ambiguousMember.Emit(context, property, property.ToDisplayString(),
						String.Join(", ", candidateProperties.Select(m => String.Format("'{0}'", m.ToDisplayString()))));
				}
				else
				{
					var candidateProperty = candidateProperties[0];

					if (!property.Type.Equals(candidateProperty.Type))
						_typeIncompatible.Emit(context, property, property.ToDisplayString(), candidateProperty.Type.ToDisplayString());

					var faultHasGetter = property.GetMethod != null;
					var faultHasSetter = property.SetMethod != null;
					var componentHasGetter = candidateProperty.GetMethod != null;
					var componentHasSetter = candidateProperty.SetMethod != null;

					var invalidGetter = !componentHasGetter && faultHasGetter;
					var invalidSetter = !componentHasSetter && faultHasSetter;

					if (invalidGetter || invalidSetter)
						_unknownPropertyPort.Emit(context, property, property.ToDisplayString(), componentSymbol.ToDisplayString(), property.Name);
				}
			}
		}
	}
}