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
	using System.Collections.Generic;
	using System.Linq;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Modeling;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;

	/// <summary>
	///     Ensures that bindings resolve to a unique pair of bound ports.
	/// </summary>
	[DiagnosticAnalyzer(LanguageNames.CSharp), UsedImplicitly]
	public class BindingAnalyzer : CSharpAnalyzer
	{
		/// <summary>
		///     The error diagnostic emitted by the analyzer when a bind method is called without a port assignment argument.
		/// </summary>
		private static readonly DiagnosticInfo ExpectedPortAssignment = DiagnosticInfo.Error(
			DiagnosticIdentifier.ExpectedPortAssignment,
			String.Format("Instances of '{0}' can only be created using port assignment syntax.", typeof(PortBinding).FullName),
			String.Format("A port assignment of the form 'component1.RequiredPorts.Port = component2.ProvidedPorts.Port' " +
						  "is required to initialize an instance of '{0}'.", typeof(PortBinding).FullName));

		/// <summary>
		///     The error diagnostic emitted by the analyzer when a bind method is called without a port assignment argument.
		/// </summary>
		private static readonly DiagnosticInfo ExpectedPortReference = DiagnosticInfo.Error(
			DiagnosticIdentifier.ExpectedPortReference,
			"Expected a reference to a port of the form 'RequiredPorts.Port' or 'ProvidedPorts.Port'.",
			"Expected a reference to a port of the form 'RequiredPorts.Port' or 'ProvidedPorts.Port'.");

		/// <summary>
		///     The error diagnostic emitted by the analyzer when a port is cast to a non-delegate type.
		/// </summary>
		private static readonly DiagnosticInfo ExpectedPortDelegateCast = DiagnosticInfo.Error(
			DiagnosticIdentifier.ExpectedPortDelegateCast,
			"Expected port to be cast to a delegate type.",
			"Expected port to be cast to a delegate type.");

		/// <summary>
		///     The error diagnostic emitted by the analyzer when a binding failed.
		/// </summary>
		private static readonly DiagnosticInfo BindingFailure = DiagnosticInfo.Error(
			DiagnosticIdentifier.BindingFailure,
			"There are no accessible signature-compatible ports that could be bound.",
			"There are no accessible signature-compatible ports that could be bound. " +
			"Candidate ports for the left-hand side: {0}. Candidate ports for the right-hand side: {1}.");

		/// <summary>
		///     The error diagnostic emitted by the analyzer when a binding is ambiguous.
		/// </summary>
		private static readonly DiagnosticInfo AmbiguousBinding = DiagnosticInfo.Error(
			DiagnosticIdentifier.AmbiguousBinding,
			"There are multiple signature-compatible ports that could be bound.",
			"Port binding is ambiguous: There are multiple accessible and signature-compatible ports " +
			"that could be bound. You can disambiguate the binding by explicitly casting one of the ports to a " +
			"delegate type with the signature of the port you intend to use. For instance, use 'RequiredPorts.X = " +
			"(Action<int>)ProvidedPorts.Y' if the port you want to bind is signature-compatible to the 'System.Action<int>' " +
			"delegate. Candidate ports for the left-hand side: {0}. Candidate ports for the right-hand side: {1}.");

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public BindingAnalyzer()
			: base(BindingFailure, AmbiguousBinding, ExpectedPortAssignment, ExpectedPortReference, ExpectedPortDelegateCast)
		{
		}

		/// <summary>
		///     Called once at session start to register actions in the analysis context.
		/// </summary>
		/// <param name="context" />
		public override void Initialize(AnalysisContext context)
		{
			context.RegisterSyntaxNodeAction(Analyze, SyntaxKind.InvocationExpression);
		}

		/// <summary>
		///     Performs the analysis on the given binding.
		/// </summary>
		/// <param name="context">The context in which the analysis should be performed.</param>
		private static void Analyze(SyntaxNodeAnalysisContext context)
		{
			var semanticModel = context.SemanticModel;
			var node = (InvocationExpressionSyntax)context.Node;

			var methodSymbol = semanticModel.GetSymbolInfo(node.Expression).Symbol as IMethodSymbol;
			if (methodSymbol == null)
				return;

			var componentBindSymbol = semanticModel.GetComponentBindMethodSymbol();
			var modelBindSymbol = semanticModel.GetModelBindMethodSymbol();

			if (!methodSymbol.Equals(componentBindSymbol) && !methodSymbol.Equals(modelBindSymbol))
				return;

			// We now expect that the argument of the invocation is a port binding in the form of an assignment
			var arguments = node.ArgumentList.Arguments;
			var argumentExpression = arguments[0].Expression.RemoveParentheses();
			if (arguments.Count != 1 || !(argumentExpression is AssignmentExpressionSyntax))
			{
				ExpectedPortAssignment.Emit(context, arguments[0].Expression);
				return;
			}

			// We now expect a port collection on both sides of the assignment
			var assignment = (AssignmentExpressionSyntax)argumentExpression;
			var leftExpression = assignment.Left.RemoveParentheses() as MemberAccessExpressionSyntax;
			var rightExpression = assignment.Right.RemoveParentheses() as MemberAccessExpressionSyntax;

			// On the right-hand side, we could also have a cast to a delegate type
			CastExpressionSyntax castExpression = null;
			if (rightExpression == null)
			{
				castExpression = assignment.Right.RemoveParentheses() as CastExpressionSyntax;
				if (castExpression != null)
					rightExpression = castExpression.Expression.RemoveParentheses() as MemberAccessExpressionSyntax;
			}

			PortCollection leftPorts;
			PortCollection rightPorts;

			if (leftExpression == null || ((leftPorts = leftExpression.GetReferencedPorts(semanticModel)) == null))
			{
				ExpectedPortReference.Emit(context, assignment.Left);
				return;
			}

			if (rightExpression == null || ((rightPorts = rightExpression.GetReferencedPorts(semanticModel)) == null))
			{
				ExpectedPortReference.Emit(context, assignment.Right);
				return;
			}

			leftPorts.RemoveInaccessiblePorts(semanticModel, node.SpanStart);
			rightPorts.RemoveInaccessiblePorts(semanticModel, node.SpanStart);

			// If either side returns an empty set of ports, we don't have to continue; this situation is handled
			// by another (more generally applicable) analyzer.
			if (leftPorts.Count == 0 || rightPorts.Count == 0)
				return;

			// If there is a cast, filter the right-hand port list
			if (castExpression != null)
			{
				var targetSymbol = castExpression.Type.GetReferencedSymbol(semanticModel) as INamedTypeSymbol;
				if (targetSymbol == null || targetSymbol.TypeKind != TypeKind.Delegate)
				{
					ExpectedPortDelegateCast.Emit(context, castExpression.Type);
					return;
				}

				rightPorts.Filter(targetSymbol);
			}

			var candidates = leftPorts.GetBindingCandidates(rightPorts);
			if (candidates.Length == 0)
				BindingFailure.Emit(context, assignment, PortSetToString(leftPorts), PortSetToString(rightPorts));
			else if (candidates.Length > 1)
				AmbiguousBinding.Emit(context, assignment, PortSetToString(candidates.Select(candidate => candidate.Left)),
					PortSetToString(candidates.Select(candidate => candidate.Right)));
		}

		/// <summary>
		///     Gets a string representation of <paramref name="ports" /> for inclusing in a diagnostic message.
		/// </summary>
		/// <param name="ports">The ports that should be included in the string.</param>
		private static string PortSetToString(IEnumerable<Port> ports)
		{
			if (!ports.Any())
				return "<none>";

			ports = ports.GroupBy(port => port.Symbol).Select(group => group.First());
			return String.Join(", ",
				ports.Select(port => String.Format("'{0}'", port.Symbol.ToDisplayString(SymbolDisplayFormat.CSharpErrorMessageFormat))));
		}
	}
}