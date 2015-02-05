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
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;
	using Utilities;

	/// <summary>
	///     Ensures that Update methods are only called by other Update methods.
	/// </summary>
	[DiagnosticAnalyzer, UsedImplicitly]
	public class UpdateInvocationAnalyzer : CSharpAnalyzer
	{
		/// <summary>
		///     The error diagnostic emitted by the analyzer.
		/// </summary>
		private static readonly DiagnosticInfo InvalidUpdateCall = DiagnosticInfo.Error(
			DiagnosticIdentifier.InvalidUpdateCall,
			"The Update() method of a component can only be called by another Update() method.",
			"'{0}' cannot be called here. The Update() method of a component can only be called by the parent component's Update() method.");

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public UpdateInvocationAnalyzer()
			: base(InvalidUpdateCall)
		{
		}

		/// <summary>
		///     Called once at session start to register actions in the analysis context.
		/// </summary>
		/// <param name="context">The analysis context that should be used to register analysis actions.</param>
		public override void Initialize(AnalysisContext context)
		{
			context.RegisterSyntaxNodeAction(Analyze, SyntaxKind.InvocationExpression);
		}

		/// <summary>
		///     Performs the analysis.
		/// </summary>
		/// <param name="context">The context in which the analysis should be performed.</param>
		private static void Analyze(SyntaxNodeAnalysisContext context)
		{
			var semanticModel = context.SemanticModel;
			var node = (InvocationExpressionSyntax)context.Node;
			var updateMethodSymbol = semanticModel.GetUpdateMethodSymbol();

			var methodSymbol = semanticModel.GetSymbolInfo(node).Symbol as IMethodSymbol;
			if (methodSymbol == null || !methodSymbol.Overrides(updateMethodSymbol))
				return;

			var parent = node.Parent;
			while (!(parent is MemberDeclarationSyntax))
				parent = parent.Parent;

			if (parent is ConstructorDeclarationSyntax)
				return;

			var symbol = semanticModel.GetDeclaredSymbol((MemberDeclarationSyntax)parent);
			if (!symbol.ContainingType.ImplementsIComponent(semanticModel))
				return;

			var parentMethod = parent as MethodDeclarationSyntax;
			if (parentMethod == null)
			{
				InvalidUpdateCall.Emit(context, node, methodSymbol.ToDisplayString());
				return;
			}

			var parentSymbol = parentMethod.GetMethodSymbol(semanticModel);
			if (!parentSymbol.Overrides(updateMethodSymbol))
				InvalidUpdateCall.Emit(context, node, methodSymbol.ToDisplayString());
		}
	}
}