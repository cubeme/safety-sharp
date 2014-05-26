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

namespace SafetySharp.CSharp.Diagnostics
{
	using System;
	using System.Linq;
	using System.Threading;
	using Extensions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Diagnostics;

	/// <summary>
	///     Checks whether the implementation of a component uses any unsupported C# syntax elements.
	/// </summary>
	[DiagnosticAnalyzer]
	[ExportDiagnosticAnalyzer(DiagnosticIdentifier, LanguageNames.CSharp)]
	internal class ComponentCSharpSyntaxAnalyzer : CSharpAnalyzer, ISemanticModelAnalyzer
	{
		private const string DiagnosticIdentifier = Compiler.DiagnosticsPrefix + "1000";

		/// <summary>
		///     Initializes a new instance of the <see cref="ComponentCSharpSyntaxAnalyzer" /> type.
		/// </summary>
		public ComponentCSharpSyntaxAnalyzer()
		{
			Error(DiagnosticIdentifier,
				  "A model component uses an unsupported C# syntax element.",
				  "C# feature is unsupported: {0}");
		}

		/// <summary>
		///     Analyzes the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model that should be analyzed.</param>
		/// <param name="addDiagnostic">A delegate that should be used to emit diagnostics.</param>
		/// <param name="cancellationToken">A token that should be checked for cancelling the analysis.</param>
		public void AnalyzeSemanticModel(SemanticModel semanticModel, Action<Diagnostic> addDiagnostic, CancellationToken cancellationToken)
		{
			Action<SyntaxNode, object> emitDiagnostic =
				(node, description) => addDiagnostic(Diagnostic.Create(Descriptor, node.GetLocation(), description));

			var componentVisitor = new ComponentVisitor(emitDiagnostic);

			var components = semanticModel
				.SyntaxTree
				.DescendantNodes<ClassDeclarationSyntax>()
				.Where(type => type.IsComponentDeclaration(semanticModel));

			foreach (var component in components)
				componentVisitor.Visit(component);
		}

		/// <summary>
		///     Checks for unsupported C# features within a component declaration.
		/// </summary>
		private class ComponentVisitor : CSharpSyntaxWalker
		{
			/// <summary>
			///     The delegate that is used to emit diagnostics.
			/// </summary>
			private readonly Action<SyntaxNode, object> _emitDiagnostic;

			/// <summary>
			///     Initializes a new instance of the <see cref="ComponentVisitor" /> type.
			/// </summary>
			/// <param name="emitDiagnostic">A delegate that should be used to emit diagnostics.</param>
			public ComponentVisitor(Action<SyntaxNode, object> emitDiagnostic)
			{
				_emitDiagnostic = emitDiagnostic;
			}

			/// <summary>
			///     Reports the node as a use of an unsupported C# feature.
			/// </summary>
			/// <param name="node">The unsupported C# syntax node.</param>
			public override void DefaultVisit(SyntaxNode node)
			{
				_emitDiagnostic(node, node.CSharpKind().ToDescription());
			}

			/// <summary>
			///     Visits the descendant nodes of <paramref name="node" />.
			/// </summary>
			/// <param name="node">The node whose descendants should be visited.</param>
			private void VisitDescendantNodes(SyntaxNode node)
			{
				base.DefaultVisit(node);
			}

			public override void VisitClassDeclaration(ClassDeclarationSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitIdentifierName(IdentifierNameSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitQualifiedName(QualifiedNameSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitAliasQualifiedName(AliasQualifiedNameSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitExternAliasDirective(ExternAliasDirectiveSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitFieldDeclaration(FieldDeclarationSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitConstructorDeclaration(ConstructorDeclarationSyntax node)
			{
				// Nothing to do here, as constructors support all C# features
			}

			public override void VisitBaseList(BaseListSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitMethodDeclaration(MethodDeclarationSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitVariableDeclaration(VariableDeclarationSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitVariableDeclarator(VariableDeclaratorSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitPredefinedType(PredefinedTypeSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitBlock(BlockSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitParameterList(ParameterListSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitReturnStatement(ReturnStatementSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitExpressionStatement(ExpressionStatementSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitInvocationExpression(InvocationExpressionSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitBinaryExpression(BinaryExpressionSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitPrefixUnaryExpression(PrefixUnaryExpressionSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitArgumentList(ArgumentListSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitArgument(ArgumentSyntax node)
			{
				VisitDescendantNodes(node);
			}

			public override void VisitLiteralExpression(LiteralExpressionSyntax node)
			{
				VisitDescendantNodes(node);
			}
		}
	}
}