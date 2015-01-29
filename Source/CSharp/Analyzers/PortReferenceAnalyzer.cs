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
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Modeling;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;
	using Utilities;

	/// <summary>
	///     Ensures that ports referenced using the <see cref="IComponent.RequiredPorts" /> or
	///     <see cref="IComponent.ProvidedPorts" /> properties are actually declared by the target class.
	/// </summary>
	[DiagnosticAnalyzer]
	public class PortReferenceAnalyzer : CSharpAnalyzer
	{
		/// <summary>
		///     Indicates that a provided port could not be found.
		/// </summary>
		private static readonly DiagnosticInfo UnknownProvidedPort = DiagnosticInfo.Error(
			DiagnosticIdentifier.UnknownProvidedPort,
			"The component does not declare a provided port of the given name.",
			"'{0}' does not declare a provided port named '{1}'.");

		/// <summary>
		///     Indicates that a required port could not be found.
		/// </summary>
		private static readonly DiagnosticInfo UnknownRequiredPort = DiagnosticInfo.Error(
			DiagnosticIdentifier.UnknownRequiredPort,
			"The component does not declare a required port of the given name.",
			"'{0}' does not declare a required port named '{1}'.");

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public PortReferenceAnalyzer()
			: base(UnknownProvidedPort, UnknownRequiredPort)
		{
		}

		/// <summary>
		///     Called once at session start to register actions in the analysis context.
		/// </summary>
		/// <param name="context" />
		public override void Initialize(AnalysisContext context)
		{
			context.RegisterSyntaxNodeAction(Analyze, SyntaxKind.SimpleMemberAccessExpression);
		}

		/// <summary>
		///     Performs the analysis.
		/// </summary>
		/// <param name="context">The context in which the analysis should be performed.</param>
		private static void Analyze(SyntaxNodeAnalysisContext context)
		{
			var semanticModel = context.SemanticModel;
			var node = (MemberAccessExpressionSyntax)context.Node;

			var symbol = semanticModel.GetSymbolInfo(node.Expression).Symbol as IPropertySymbol;
			if (symbol == null)
				return;

			var requiredPortsSymbol = (IPropertySymbol)semanticModel.GetComponentClassSymbol().GetMembers("RequiredPorts").Single();
			var providedPortsSymbol = (IPropertySymbol)semanticModel.GetComponentClassSymbol().GetMembers("ProvidedPorts").Single();

			if (!symbol.Overrides(requiredPortsSymbol) && !symbol.Overrides(providedPortsSymbol))
			{
				// Try the interface properties; thanks to F#, Component implements those properties explicitly...
				requiredPortsSymbol = (IPropertySymbol)semanticModel.GetComponentInterfaceSymbol().GetMembers("RequiredPorts").Single();
				providedPortsSymbol = (IPropertySymbol)semanticModel.GetComponentInterfaceSymbol().GetMembers("ProvidedPorts").Single();

				if (!symbol.Overrides(requiredPortsSymbol) && !symbol.Overrides(providedPortsSymbol))
					return;
			}

			var portName = node.Name.Identifier.ValueText;
			var isRequiredPort = symbol.Equals(requiredPortsSymbol);
			var nestedMemberAccess = node.Expression as MemberAccessExpressionSyntax;

			ITypeSymbol targetSymbol = null;
			if (nestedMemberAccess == null)
				targetSymbol = semanticModel.GetEnclosingSymbol(node.SpanStart).ContainingType;
			else
			{
				var untypedTargetSymbol = nestedMemberAccess.Expression.GetReferencedSymbol(semanticModel);

				var parameterSymbol = untypedTargetSymbol as IParameterSymbol;
				var localSymbol = untypedTargetSymbol as ILocalSymbol;
				var fieldSymbol = untypedTargetSymbol as IFieldSymbol;
				var propertySymbol = untypedTargetSymbol as IPropertySymbol;
				var methodSymbol = untypedTargetSymbol as IMethodSymbol;

				if (parameterSymbol != null)
					targetSymbol = parameterSymbol.Type;

				if (localSymbol != null)
					targetSymbol = localSymbol.Type;

				if (fieldSymbol != null)
					targetSymbol = fieldSymbol.Type;

				if (propertySymbol != null)
					targetSymbol = propertySymbol.Type;

				if (methodSymbol != null)
					targetSymbol = methodSymbol.ReturnType;
			}

			Assert.NotNull(targetSymbol, "Failed to determine the target symbol.");

			if (isRequiredPort && targetSymbol.GetRequiredPorts(semanticModel, node.SpanStart).All(p => p.Name != portName))
				UnknownRequiredPort.Emit(context, node.Name, targetSymbol.ToDisplayString(SymbolDisplayFormat.CSharpErrorMessageFormat), portName);

			if (!isRequiredPort && targetSymbol.GetProvidedPorts(semanticModel, node.SpanStart).All(p => p.Name != portName))
				UnknownProvidedPort.Emit(context, node.Name, targetSymbol.ToDisplayString(SymbolDisplayFormat.CSharpErrorMessageFormat), portName);
		}
	}
}