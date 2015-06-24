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

namespace SafetySharp.Compiler.Normalization
{
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using System.Runtime.CompilerServices;
	using CompilerServices;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Quotations;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;
	using Runtime;

	/// <summary>
	///     Normalizes the bodies of analyzable methods. For instance:
	///     <code>
	///     int M()
	///     {
	///         return 1;
	///     }
	/// 
	///     // becomes
	/// 
	///     [MethodBodyMetadata("MImpl")]
	///     int M()
	///     {
	///         return 1;
	///     }
	/// 
	///     private BlockStatement MImpl()
	///     {
	///         return new BlockStatement(new ReturnStatement(new IntegerLiteralExpression(1)));
	///     }
	///     </code>
	/// </summary>
	public sealed class MethodBodyNormalizer : SyntaxNormalizer
	{
		/// <summary>
		///     The rewritten methods that contain the method body metadata.
		/// </summary>
		private Dictionary<string, BlockSyntax> _implementationMethods;

		/// <summary>
		///     The number of method body metadata methods that have been generated for the compilation;
		/// </summary>
		private int _methodCount;

		/// <summary>
		///     Normalizes the syntax trees of the <see cref="Compilation" />.
		/// </summary>
		protected override Compilation Normalize()
		{
			var compilation = Compilation;

			compilation = ApplyNormalizer<ExpressionMethodNormalizer>(compilation, Syntax);
			compilation = ApplyNormalizer<LocalVariablesNormalizer>(compilation, Syntax);
			compilation = ApplyNormalizer<SwitchStatementNormalizer>(compilation, Syntax);
			compilation = ApplyNormalizer<BlockNormalizer>(compilation, Syntax);
			compilation = ApplyNormalizer<OptionalArgumentNormalizer>(compilation, Syntax);
			compilation = ApplyNormalizer<NamedArgumentNormalizer>(compilation, Syntax);
			compilation = ApplyNormalizer<CompoundAssignmentNormalizer>(compilation, Syntax);
			compilation = ApplyNormalizer<SideEffectsNormalizer>(compilation, Syntax);
			compilation = ApplyNormalizer<SingleExitPointNormalizer>(compilation, Syntax);
			compilation = ApplyNormalizer<MethodBodyCreationNormalizer>(compilation, Syntax);

			_implementationMethods =
				(from syntaxTree in compilation.SyntaxTrees
				 from methodDeclaration in syntaxTree.Descendants<MethodDeclarationSyntax>()
				 let semanticModel = compilation.GetSemanticModel(syntaxTree)
				 let methodSymbol = methodDeclaration.GetMethodSymbol(semanticModel)
				 where methodDeclaration.GenerateMethodBodyMetadata(semanticModel)
				 select new { Key = GetMethodKey(methodSymbol), MethodBody = methodDeclaration.Body })
					.ToDictionary(m => m.Key, m => m.MethodBody);

			return base.Normalize();
		}

		/// <summary>
		///     Gets the key the <paramref name="methodSymbol" /> is stored under in the <seealso cref="_implementationMethods" />
		///     dictionary.
		/// </summary>
		/// <param name="methodSymbol">The method the key should be returned for.</param>
		private static string GetMethodKey(IMethodSymbol methodSymbol)
		{
			return String.Format("{0} {1}", methodSymbol.ContainingType.ToDisplayString(), methodSymbol.ToDisplayString());
		}

		/// <summary>
		///     Normalizes the <paramref name="methodDeclaration" />.
		/// </summary>
		/// <param name="methodDeclaration">The method declaration that should be normalized.</param>
		public override SyntaxNode VisitMethodDeclaration(MethodDeclarationSyntax methodDeclaration)
		{
			if (!methodDeclaration.GenerateMethodBodyMetadata(SemanticModel))
				return methodDeclaration;

			var methodSymbol = methodDeclaration.GetMethodSymbol(SemanticModel);
			var methodBody = _implementationMethods[GetMethodKey(methodSymbol)];
			var metadataMethodName = (methodDeclaration.Identifier.ValueText + "MethodBody" + _methodCount++).ToSynthesized();

			var metadataMethod = Syntax.MethodDeclaration(
				name: metadataMethodName,
				returnType: Syntax.TypeExpression(Compilation.GetTypeSymbol<MethodBodyMetadata>()),
				accessibility: Accessibility.Private,
				statements: methodBody.Statements);

			var suppressAttribute = Syntax.Attribute(typeof(SuppressTransformationAttribute).FullName);
			var compilerGeneratedAttribute = Syntax.Attribute(typeof(CompilerGeneratedAttribute).FullName);

			metadataMethod = Syntax.AddAttributes(metadataMethod, suppressAttribute, compilerGeneratedAttribute);
			AddMembers(methodSymbol.ContainingType, (MethodDeclarationSyntax)metadataMethod);

			var metadataAttribute = Syntax.Attribute(typeof(MethodBodyMetadataAttribute).FullName, Syntax.LiteralExpression(metadataMethodName));
			return Syntax.AddAttributes(methodDeclaration, metadataAttribute);
		}
	}
}