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
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;
	using Runtime.Modeling;

	/// <summary>
	///     Ensures that no instances of the <see cref="PortBinding" /> class are created explicitly.
	/// </summary>
	[DiagnosticAnalyzer(LanguageNames.CSharp), UsedImplicitly]
	public sealed class PortBindingInstantiationAnalyzer : Analyzer
	{
		/// <summary>
		///     The error diagnostic emitted by the analyzer.
		/// </summary>
		private static readonly DiagnosticInfo ExplicitPortBindingInstantiation = DiagnosticInfo.Error(
			DiagnosticIdentifier.ExplicitPortBindingInstantiation,
			String.Format("Cannot instantiate an object of type '{0}' using regular constructor syntax. Use a binding expression of " +
						  "the form 'RequiredPorts.X = ProvidedPorts.Y' instead.", typeof(PortBinding).FullName),
			String.Format("Cannot instantiate an object of type '{0}' using regular constructor syntax. Use a binding expression of " +
						  "the form 'RequiredPorts.X = ProvidedPorts.Y' instead.", typeof(PortBinding).FullName));

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public PortBindingInstantiationAnalyzer()
			: base(ExplicitPortBindingInstantiation)
		{
		}

		/// <summary>
		///     Called once at session start to register actions in the analysis context.
		/// </summary>
		/// <param name="context">The analysis context that should be used to register analysis actions.</param>
		public override void Initialize(AnalysisContext context)
		{
			context.RegisterSyntaxNodeAction(Analyze, SyntaxKind.ObjectCreationExpression);
		}

		/// <summary>
		///     Performs the analysis.
		/// </summary>
		/// <param name="context">The context in which the analysis should be performed.</param>
		private static void Analyze(SyntaxNodeAnalysisContext context)
		{
			var semanticModel = context.SemanticModel;
			var node = (ObjectCreationExpressionSyntax)context.Node;

			var typeSymbol = node.Type.GetReferencedSymbol(semanticModel);
			if (typeSymbol.Equals(semanticModel.GetTypeSymbol<PortBinding>()))
				ExplicitPortBindingInstantiation.Emit(context, node);
		}
	}
}