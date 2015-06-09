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
		private static readonly DiagnosticInfo UnknownMethodPort = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectUnknownMethodPort,
			"Fault methods must override existing method ports of the affected component.",
			"Invalid fault method '{0}': Affected component of type '{1}' does not declare a method named '{2}'.");

		/// <summary>
		///     Indicates that the fault effect overrides an unknown property port.
		/// </summary>
		private static readonly DiagnosticInfo UnknownPropertyPort = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectUnknownPropertyPort,
			"Fault properties must override existing property ports of the affected component.",
			"Invalid fault property '{0}': Affected component of type '{1}' does not declare a property named '{2}' with the corresponding accessors.");

		/// <summary>
		///     Indicates that the fault effect overrides an unknown port.
		/// </summary>
		private static readonly DiagnosticInfo SignatureIncompatible = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectSignatureIncompatible,
			"Fault effects must be signature compatible with the overriden port of the affected component.",
			"Fault effect '{0}' is not signature compatible with '{1}' or any of its overloads.");

		/// <summary>
		///     Indicates that the fault effect overrides a property port of a different type.
		/// </summary>
		private static readonly DiagnosticInfo TypeIncompatible = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectIncompatibleType,
			"Fault effect properties must be declared with the type of the overriden property port of the affected component.",
			"Fault effect '{0}' must be a property of type '{1}'.");

		/// <summary>
		///     Indicates that the fault effect overrides a member of a base class.
		/// </summary>
		private static readonly DiagnosticInfo BaseMember = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectBaseMember,
			"Fault effects can only override members declared by the affected component.",
			"Fault effect '{0}' cannot affect inherited member '{1}'.");

		/// <summary>
		///     Indicates that the fault effect declares an optional parameter.
		/// </summary>
		private static readonly DiagnosticInfo OptionalParameter = DiagnosticInfo.Error(
			DiagnosticIdentifier.FaultEffectOptionalParameter,
			"Fault effects cannot declare optional parameters.",
			"Invalid optional parameter '{0}' declared by fault effect '{1}'.");

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public FaultEffectAnalyzer()
			: base(
				UnknownMethodPort, UnknownPropertyPort, SignatureIncompatible, BaseMember, OptionalParameter, TypeIncompatible)
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

			var faultMethods = faultSymbol.GetMembers().OfType<IMethodSymbol>().Where(candidate => candidate.MethodKind == MethodKind.Ordinary);
			foreach (var method in faultMethods)
			{
				var optionalParameter = method.Parameters.FirstOrDefault(parameter => parameter.IsOptional);
				if (optionalParameter != null)
					OptionalParameter.Emit(context, optionalParameter, optionalParameter.Name, method.ToDisplayString());

				var candidateMethods = componentSymbol
					.GetMembers(method.Name)
					.OfType<IMethodSymbol>()
					.Where(candidate => candidate.MethodKind == MethodKind.Ordinary)
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
						BaseMember.Emit(context, method, method.ToDisplayString(), baseCandidateMethods[0].ToDisplayString());
					else
						UnknownMethodPort.Emit(context, method, method.ToDisplayString(), componentSymbol.ToDisplayString(), method.Name);

					continue;
				}

				var overriddenMethod = candidateMethods.SingleOrDefault(candidate => candidate.IsSignatureCompatibleTo(method));
				if (overriddenMethod == null)
					SignatureIncompatible.Emit(context, method, method.ToDisplayString(), candidateMethods[0].ToDisplayString());
			}

			var faultProperties = faultSymbol.GetMembers().OfType<IPropertySymbol>();
			foreach (var property in faultProperties)
			{
				var overriddenProperty = componentSymbol.GetMembers(property.Name).OfType<IPropertySymbol>().FirstOrDefault();
				if (overriddenProperty == null)
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
						BaseMember.Emit(context, property, property.ToDisplayString(), baseProperty.ToDisplayString());
					else
						UnknownPropertyPort.Emit(context, property, property.ToDisplayString(), componentSymbol.ToDisplayString(), property.Name);
				}
				else
				{
					if (!property.Type.Equals(overriddenProperty.Type))
						TypeIncompatible.Emit(context, property, property.ToDisplayString(), overriddenProperty.Type.ToDisplayString());

					var faultHasGetter = property.GetMethod != null;
					var faultHasSetter = property.SetMethod != null;
					var componentHasGetter = overriddenProperty.GetMethod != null;
					var componentHasSetter = overriddenProperty.SetMethod != null;

					var invalidGetter = !componentHasGetter && faultHasGetter;
					var invalidSetter = !componentHasSetter && faultHasSetter;

					if (invalidGetter || invalidSetter)
						UnknownPropertyPort.Emit(context, property, property.ToDisplayString(), componentSymbol.ToDisplayString(), property.Name);
				}
			}
		}
	}
}