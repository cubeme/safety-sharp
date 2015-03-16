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
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Diagnostics;
	using QuickGraph;
	using QuickGraph.Algorithms;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;
	using Utilities;

	/// <summary>
	///     Ensures that there is no static recursion within a component.
	/// </summary>
	[DiagnosticAnalyzer(LanguageNames.CSharp), UsedImplicitly]
	public class RecursionAnalyzer : CSharpAnalyzer
	{
		/// <summary>
		///     The error diagnostic emitted by the analyzer when a recursive call is made.
		/// </summary>
		private static readonly DiagnosticInfo Recursion = DiagnosticInfo.Error(
			DiagnosticIdentifier.Recursion,
			"Recursive method or property accessor invocation is not allowed.",
			"Recursive method or property accessor invocation is not allowed here.");

		/// <summary>
		///     The error diagnostic emitted by the analyzer when recursive call cycle is detected.
		/// </summary>
		private static readonly DiagnosticInfo MutualRecursion = DiagnosticInfo.Error(
			DiagnosticIdentifier.MutualRecursion,
			"Mutually recursive method or property accessor invocations are not allowed.",
			"Mutually recursive method or property accessor invocations are not allowed here. The recursion involves: {0}.");

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public RecursionAnalyzer()
			: base(Recursion, MutualRecursion)
		{
		}

		/// <summary>
		///     Called once at session start to register actions in the analysis context.
		/// </summary>
		/// <param name="context">The analysis context that should be used to register analysis actions.</param>
		public override void Initialize(AnalysisContext context)
		{
			context.RegisterSemanticModelAction(Analyze);
		}

		/// <summary>
		///     Performs the analysis.
		/// </summary>
		/// <param name="context">The context in which the analysis should be performed.</param>
		private static void Analyze(SemanticModelAnalysisContext context)
		{
			foreach (var node in context.SemanticModel.SyntaxTree.Descendants<ClassDeclarationSyntax>())
				Analyze(context, node);
		}

		/// <summary>
		///     Performs the analysis.
		/// </summary>
		/// <param name="context">The context in which the analysis should be performed.</param>
		/// <param name="node">The class declaration that should be analyzed.</param>
		private static void Analyze(SemanticModelAnalysisContext context, ClassDeclarationSyntax node)
		{
			var semanticModel = context.SemanticModel;

			var classSymbol = semanticModel.GetDeclaredSymbol(node);
			if (!classSymbol.IsDerivedFromComponent(semanticModel))
				return;

			var methods = node.Descendants<MethodDeclarationSyntax>().ToArray();
			var accessors = node.Descendants<PropertyDeclarationSyntax>().SelectMany(property => property.AccessorList.Accessors).ToArray();

			var methodEdges = methods.SelectMany(method =>
			{
				var symbol = method.GetMethodSymbol(semanticModel);
				var source = new InvocationInfo(method, symbol);
				return GetInvocations(method, semanticModel)
					.Select(invocation => new SEquatableEdge<InvocationInfo>(source, invocation));
			});

			var accessorEdges = accessors.SelectMany(accessor =>
			{
				var symbol = semanticModel.GetDeclaredSymbol(accessor);
				var source = new InvocationInfo(accessor, symbol);
				return GetInvocations(accessor, semanticModel)
					.Select(invocation => new SEquatableEdge<InvocationInfo>(source, invocation));
			});

			// Check for recursive function calls; this is a special case that is not detected by the
			// SSC-based cycle detection below.
			var edges = methodEdges.Concat(accessorEdges).ToArray();
			foreach (var edge in edges.Where(e => e.Source.Equals(e.Target)))
				Recursion.Emit(context, edge.Target.Node);

			// Construct the sets of strongly connected components of the graph; if there are no cycles, the
			// number of SCCs matches the number of vertices.
			IDictionary<InvocationInfo, int> components;
			var graph = edges.ToAdjacencyGraph<InvocationInfo, SEquatableEdge<InvocationInfo>>();
			var componentCount = graph.StronglyConnectedComponents(out components);

			if (componentCount == graph.VertexCount)
				return;

			// Report all cycles
			var cycles = from pair in components
						 group pair by pair.Value
						 into groups
						 where groups.Count() > 1
						 select groups;

			foreach (var cycle in cycles)
			{
				var info = String.Join(", ", cycle.Select(c => String.Format("'{0}'", c.Key.Symbol.ToDisplayString())));
				MutualRecursion.Emit(context, cycle.First().Key.Symbol.Locations[0], info);
			}
		}

		/// <summary>
		///     Gets all method, getter, and setter invocations within <paramref name="memberDeclaration" />.
		/// </summary>
		/// <param name="memberDeclaration">The member declaration the invocations should be returned for.</param>
		/// <param name="semanticModel">The semantic model that should be used to look up symbols.</param>
		private static IEnumerable<InvocationInfo> GetInvocations(SyntaxNode memberDeclaration, SemanticModel semanticModel)
		{
			var methodInvocations = from invocation in memberDeclaration.Descendants<InvocationExpressionSyntax>()
									select new InvocationInfo(invocation, (IMethodSymbol)semanticModel.GetSymbolInfo(invocation).Symbol);

			var setterInvocations = from assignment in memberDeclaration.Descendants<AssignmentExpressionSyntax>()
									let symbol = semanticModel.GetSymbolInfo(assignment.Left).Symbol as IPropertySymbol
									where symbol != null
									select new InvocationInfo(assignment.Left, symbol.SetMethod);

			var getterInvocations = from identifier in memberDeclaration.Descendants<IdentifierNameSyntax>()
									let symbol = semanticModel.GetSymbolInfo(identifier).Symbol as IPropertySymbol
									where symbol != null && !IsAssignmentTarget(identifier)
									select new InvocationInfo(identifier, symbol.GetMethod);

			return methodInvocations.Concat(setterInvocations).Concat(getterInvocations);
		}

		/// <summary>
		///     Gets a value indicating whether <paramref name="node" /> is the target of an assignment.
		/// </summary>
		/// <param name="node">The syntax node that should be checked.</param>
		private static bool IsAssignmentTarget(SyntaxNode node)
		{
			while (!(node.Parent is MemberDeclarationSyntax) && !(node.Parent is AssignmentExpressionSyntax))
				node = node.Parent;

			var assignment = node.Parent as AssignmentExpressionSyntax;
			return assignment != null && assignment.Left == node;
		}

		/// <summary>
		///     Describes an invocation of a method or property accessor.
		/// </summary>
		private struct InvocationInfo : IEquatable<InvocationInfo>
		{
			/// <summary>
			///     The syntax node that invokes the method or property accessor.
			/// </summary>
			public readonly SyntaxNode Node;

			/// <summary>
			///     The symbol of the invoked method or property accessor.
			/// </summary>
			public readonly IMethodSymbol Symbol;

			/// <summary>
			///     Initializes a new instance.
			/// </summary>
			public InvocationInfo(SyntaxNode node, IMethodSymbol symbol)
			{
				Node = node;
				Symbol = symbol;
			}

			/// <summary>
			///     Indicates whether the current object is equal to another object of the same type.
			/// </summary>
			/// <param name="other">An object to compare with this object.</param>
			public bool Equals(InvocationInfo other)
			{
				return Symbol.Equals(other.Symbol);
			}

			/// <summary>
			///     Indicates whether this instance and a specified object are equal.
			/// </summary>
			/// <param name="obj">Another object to compare to. </param>
			public override bool Equals(object obj)
			{
				if (ReferenceEquals(null, obj))
					return false;

				return obj is InvocationInfo && Equals((InvocationInfo)obj);
			}

			/// <summary>
			///     Returns the hash code for this instance.
			/// </summary>
			public override int GetHashCode()
			{
				return Symbol.GetHashCode();
			}
		}
	}
}