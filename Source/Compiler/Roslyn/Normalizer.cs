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

namespace SafetySharp.Compiler.Roslyn
{
	using System;
	using System.IO;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Editing;
	using Syntax;
	using Utilities;

	/// <summary>
	///     A base class for C# normalizers that normalize certain C# language features.
	/// </summary>
	public abstract class Normalizer : CSharpSyntaxRewriter
	{
		/// <summary>
		///     The syntax tree that is currently being normalized.
		/// </summary>
		private SyntaxTree _syntaxTree;

		/// <summary>
		///     Gets the compilation that is currently being normalized.
		/// </summary>
		protected Compilation Compilation { get; private set; }

		/// <summary>
		///     Gets the semantic model that should be used for semantic analysis during normalization.
		/// </summary>
		protected SemanticModel SemanticModel { get; private set; }

		/// <summary>
		///     Gets the syntax generator that the normalizer can use to generate syntax nodes.
		/// </summary>
		protected SyntaxGenerator Syntax { get; private set; }

		/// <summary>
		///     Normalizes the <paramref name="compilation" />.
		/// </summary>
		/// <param name="compilation">The compilation that should be normalized.</param>
		/// <param name="syntaxGenerator">The syntax generator that the normalizer should use to generate syntax nodes.</param>
		[NotNull]
		public Compilation Normalize([NotNull] Compilation compilation, [NotNull] SyntaxGenerator syntaxGenerator)
		{
			Requires.NotNull(compilation, () => compilation);

			Syntax = syntaxGenerator;
			Compilation = compilation;

			return Normalize();
		}

		/// <summary>
		///     Normalizes the <see cref="Compilation" />.
		/// </summary>
		protected virtual Compilation Normalize()
		{
			return NormalizeSyntaxTrees();
		}

		/// <summary>
		///     Normalizes all syntax trees of the <see cref="Compilation" />.
		/// </summary>
		protected Compilation NormalizeSyntaxTrees()
		{
			foreach (var syntaxTree in Compilation.SyntaxTrees)
			{
				_syntaxTree = syntaxTree;

				var normalizedSyntaxTree = Normalize(syntaxTree);
				Compilation = Compilation.ReplaceSyntaxTree(syntaxTree, normalizedSyntaxTree);
			}

			return Compilation;
		}

		/// <summary>
		///     Normalizes the <paramref name="syntaxTree" /> of the <see cref="Compilation" />.
		/// </summary>
		/// <param name="syntaxTree">The syntax tree that should be normalized.</param>
		protected virtual SyntaxTree Normalize(SyntaxTree syntaxTree)
		{
			SemanticModel = Compilation.GetSemanticModel(syntaxTree);

			var root = syntaxTree.GetRoot();
			var normalizedRoot = Visit(root);

			if (root == normalizedRoot)
				return syntaxTree;

			return syntaxTree.WithRoot(normalizedRoot);
		}

		/// <summary>
		///     Adds the <paramref name="compilationUnit" /> to the normalized compilation.
		/// </summary>
		/// <param name="compilationUnit">The compilation unit that should be added.</param>
		protected void AddCompilationUnit([NotNull] CompilationUnitSyntax compilationUnit)
		{
			Requires.NotNull(compilationUnit, () => compilationUnit);

			var originalPath = _syntaxTree.FilePath ?? String.Empty;
			var path = String.Format("{0}.g.cs{1}", Path.GetFileNameWithoutExtension(originalPath), Guid.NewGuid());
			var syntaxTree = _syntaxTree.WithRoot(compilationUnit.NormalizeWhitespace()).WithFilePath(path);

			Compilation = Compilation.AddSyntaxTrees(syntaxTree);
		}

		/// <summary>
		///     Adds a compilation unit containing a part of the partial <paramref name="type" /> containing the
		///     <paramref name="members" />.
		/// </summary>
		/// <param name="type">The type the part should be declared for.</param>
		/// <param name="members">The members that should be added to the class.</param>
		protected void AddMembers([NotNull] INamedTypeSymbol type, [NotNull] params MemberDeclarationSyntax[] members)
		{
			Requires.NotNull(type, () => type);
			Requires.NotNull(members, () => members);

			var generatedClass = SyntaxFactory
				.ClassDeclaration(type.Name)
				//.WithTypeParameterList(classDeclaration.TypeParameterList)
				.WithMembers(SyntaxFactory.List(members))
				.WithModifiers(SyntaxFactory.TokenList(SyntaxFactory.Token(SyntaxKind.PartialKeyword)));

			CompilationUnitSyntax compilationUnit;

			if (type.ContainingType != null)
			{
				generatedClass = SyntaxFactory
					.ClassDeclaration(type.ContainingType.Name)
					//.WithTypeParameterList(classDeclaration.Ancestors().OfType<ClassDeclarationSyntax>().First().TypeParameterList)
					.WithMembers(SyntaxFactory.SingletonList((MemberDeclarationSyntax)generatedClass))
					.WithModifiers(SyntaxFactory.TokenList(SyntaxFactory.Token(SyntaxKind.PartialKeyword)));
			}

			if (type.ContainingNamespace != null && !type.ContainingNamespace.IsGlobalNamespace)
			{
				var namespaceName = SyntaxFactory.ParseName(type.ContainingNamespace.ToDisplayString());
				var namespaceDeclaration = SyntaxFactory
					.NamespaceDeclaration(namespaceName)
					.WithMembers(SyntaxFactory.SingletonList((MemberDeclarationSyntax)generatedClass));

				compilationUnit = SyntaxFactory
					.CompilationUnit()
					.WithMembers(SyntaxFactory.SingletonList((MemberDeclarationSyntax)namespaceDeclaration));
			}
			else
			{
				compilationUnit = SyntaxFactory
					.CompilationUnit()
					.WithMembers(SyntaxFactory.SingletonList((MemberDeclarationSyntax)generatedClass));
			}

			AddCompilationUnit(compilationUnit);
		}
	}
}