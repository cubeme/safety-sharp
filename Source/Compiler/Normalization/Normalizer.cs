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
	using CSharp.Roslyn;
	using CSharp.Roslyn.Syntax;
	using CSharp.Utilities;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;

	/// <summary>
	///     A base class for C# normalizers that normalize certain S# language features in order to
	///     ensure that the S# models remain executable.
	/// </summary>
	public abstract class Normalizer : CSharpSyntaxRewriter
	{
		/// <summary>
		///     The scope of the normalizer.
		/// </summary>
		private readonly NormalizationScope _scope;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="scope">The scope of the normalizer.</param>
		protected Normalizer(NormalizationScope scope)
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

			return syntaxTree.WithChangedText(normalizedRoot.GetText(syntaxTree.GetText().Encoding));
		}

		/// <summary>
		///     Ensures that the <paramref name="classDeclaration" /> is only normalized when the normalizer has the appropriate
		///     <see cref="NormalizationScope" />.
		/// </summary>
		[NotNull, Pure]
		public override sealed SyntaxNode VisitClassDeclaration([NotNull] ClassDeclarationSyntax classDeclaration)
		{
			if (ShouldNormalizeClassDeclaration(classDeclaration))
				return NormalizeClassDeclaration((ClassDeclarationSyntax)base.VisitClassDeclaration(classDeclaration));

			// We still might have to normalize nested types, though
			var originalDeclaration = classDeclaration;
			foreach (var nestedType in originalDeclaration.Descendants<BaseTypeDeclarationSyntax>())
				classDeclaration = classDeclaration.ReplaceNode(nestedType, Visit(nestedType));

			return classDeclaration;
		}

		/// <summary>
		///     Ensures that the <paramref name="interfaceDeclaration" /> is only normalized when the normalizer has the appropriate
		///     <see cref="NormalizationScope" />.
		/// </summary>
		[NotNull, Pure]
		public override sealed SyntaxNode VisitInterfaceDeclaration([NotNull] InterfaceDeclarationSyntax interfaceDeclaration)
		{
			if (ShouldNormalizeInterfaceDeclaration(interfaceDeclaration))
				return NormalizeInterfaceDeclaration((InterfaceDeclarationSyntax)base.VisitInterfaceDeclaration(interfaceDeclaration));

			return interfaceDeclaration;
		}

		/// <summary>
		///     Ensures that the <paramref name="constructorDeclaration" /> is only normalized when the normalizer has the appropriate
		///     <see cref="NormalizationScope" />.
		/// </summary>
		[NotNull, Pure]
		public override sealed SyntaxNode VisitConstructorDeclaration([NotNull] ConstructorDeclarationSyntax constructorDeclaration)
		{
			if (_scope.HasFlag(NormalizationScope.Global) || !_scope.HasFlag(NormalizationScope.ComponentStatements))
				return NormalizeConstructorDeclaration((ConstructorDeclarationSyntax)base.VisitConstructorDeclaration(constructorDeclaration));

			return constructorDeclaration;
		}

		/// <summary>
		///     Normalizes the <paramref name="classDeclaration" />.
		/// </summary>
		[NotNull, Pure]
		protected virtual ClassDeclarationSyntax NormalizeClassDeclaration([NotNull] ClassDeclarationSyntax classDeclaration)
		{
			return classDeclaration;
		}

		/// <summary>
		///     Normalizes the <paramref name="interfaceDeclaration" />.
		/// </summary>
		[NotNull, Pure]
		protected virtual InterfaceDeclarationSyntax NormalizeInterfaceDeclaration([NotNull] InterfaceDeclarationSyntax interfaceDeclaration)
		{
			return interfaceDeclaration;
		}

		/// <summary>
		///     Normalizes the <paramref name="constructorDeclaration" />.
		/// </summary>
		[NotNull, Pure]
		protected virtual ConstructorDeclarationSyntax NormalizeConstructorDeclaration(
			[NotNull] ConstructorDeclarationSyntax constructorDeclaration)
		{
			return constructorDeclaration;
		}

		/// <summary>
		///     Checks whether <paramref name="classDeclaration" /> should be normalized.
		/// </summary>
		[Pure]
		private bool ShouldNormalizeClassDeclaration([NotNull] ClassDeclarationSyntax classDeclaration)
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
		private bool ShouldNormalizeInterfaceDeclaration([NotNull] InterfaceDeclarationSyntax interfaceDeclaration)
		{
			if (_scope.HasFlag(NormalizationScope.Global))
				return true;

			return _scope.HasFlag(NormalizationScope.ComponentInterfaces) && interfaceDeclaration.ImplementsIComponent(SemanticModel);
		}
	}
}