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

namespace SafetySharp.CSharpCompiler.Roslyn
{
	using System;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Syntax;
	using Utilities;

	/// <summary>
	///     A base class for C# normalizers that normalize certain SafetySharp C# language features in order to
	///     ensure that the SafetySharp models remain executable.
	/// </summary>
	public abstract class CSharpNormalizer : CSharpSyntaxRewriter
	{
		/// <summary>
		///     The scope of the normalizer.
		/// </summary>
		private readonly NormalizationScope _scope;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="scope">The scope of the normalizer.</param>
		protected CSharpNormalizer(NormalizationScope scope)
		{
			_scope = scope;
		}

		/// <summary>
		///     Gets the semantic model that should be used for semantic analysis during normalization.
		/// </summary>
		protected SemanticModel SemanticModel { get; private set; }

		/// <summary>
		///     Normalizes the C# code contained in <paramref name="compilation" />.
		/// </summary>
		/// <param name="compilation">The compilation that contains the code that should be normalized.</param>
		[NotNull, Pure]
		public Compilation Normalize([NotNull] Compilation compilation)
		{
			Requires.NotNull(compilation, () => compilation);

			foreach (var syntaxTree in compilation.SyntaxTrees)
				compilation = compilation.ReplaceSyntaxTree(syntaxTree, Normalize(compilation, syntaxTree));

			return compilation;
		}

		/// <summary>
		///     Normalizes the <paramref name="syntaxTree" /> of the <paramref name="compilation." />
		/// </summary>
		/// <param name="compilation">The compilation that contains the <paramref name="syntaxTree." /></param>
		/// <param name="syntaxTree">The syntax tree that should be normalized.</param>
		[NotNull, Pure]
		private SyntaxTree Normalize([NotNull] Compilation compilation, [NotNull] SyntaxTree syntaxTree)
		{
			SemanticModel = compilation.GetSemanticModel(syntaxTree);

			var root = syntaxTree.GetRoot();
			var normalizedRoot = Visit(root);

			if (root == normalizedRoot)
				return syntaxTree;

			return syntaxTree.WithChangedText(normalizedRoot.GetText());
		}

		/// <summary>
		///     Ensures that the <paramref name="classDeclaration" /> is only normalized when the normalizer has the appropriate
		///     <see cref="NormalizationScope" />.
		/// </summary>
		[NotNull, Pure]
		public override SyntaxNode VisitClassDeclaration([NotNull] ClassDeclarationSyntax classDeclaration)
		{
			if (ShouldNormalizeClassDeclaration(classDeclaration))
				return base.VisitClassDeclaration(classDeclaration);

			return classDeclaration;
		}

		/// <summary>
		///     Ensures that the <paramref name="interfaceDeclaration" /> is only normalized when the normalizer has the appropriate
		///     <see cref="NormalizationScope" />.
		/// </summary>
		[NotNull, Pure]
		public override SyntaxNode VisitInterfaceDeclaration([NotNull] InterfaceDeclarationSyntax interfaceDeclaration)
		{
			if (ShouldNormalizeInterfaceDeclaration(interfaceDeclaration))
				return base.VisitInterfaceDeclaration(interfaceDeclaration);

			return interfaceDeclaration;
		}

		/// <summary>
		///     Ensures that the <paramref name="constructorDeclaration" /> is only normalized when the normalizer has the appropriate
		///     <see cref="NormalizationScope" />.
		/// </summary>
		[NotNull, Pure]
		public override SyntaxNode VisitConstructorDeclaration([NotNull] ConstructorDeclarationSyntax constructorDeclaration)
		{
			if (ShouldNormalizeConstructorDeclaration(constructorDeclaration))
				return base.VisitConstructorDeclaration(constructorDeclaration);

			return constructorDeclaration;
		}

		/// <summary>
		///     Checks whether <paramref name="classDeclaration" /> should be normalized.
		/// </summary>
		[Pure]
		protected bool ShouldNormalizeClassDeclaration([NotNull] ClassDeclarationSyntax classDeclaration)
		{
			if (_scope.HasFlag(NormalizationScope.Global))
				return true;

			if (!_scope.HasFlag(NormalizationScope.Components) && !_scope.HasFlag(NormalizationScope.ComponentStatements))
				return false;

			return classDeclaration.IsDerivedFromComponent(SemanticModel);
		}

		/// <summary>
		///     Checks whether <paramref name="interfaceDeclaration" /> should be normalized.
		/// </summary>
		[Pure]
		protected bool ShouldNormalizeInterfaceDeclaration([NotNull] InterfaceDeclarationSyntax interfaceDeclaration)
		{
			if (_scope.HasFlag(NormalizationScope.Global))
				return true;

			return _scope.HasFlag(NormalizationScope.ComponentInterfaces) && interfaceDeclaration.ImplementsIComponent(SemanticModel);
		}

		/// <summary>
		///     Checks whether <paramref name="constructorDeclaration" /> should be normalized.
		/// </summary>
		[Pure]
		protected bool ShouldNormalizeConstructorDeclaration([NotNull] ConstructorDeclarationSyntax constructorDeclaration)
		{
			return _scope.HasFlag(NormalizationScope.Global) || !_scope.HasFlag(NormalizationScope.ComponentStatements);
		}
	}
}