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

namespace SafetySharp.CSharp.Roslyn.Syntax
{
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with <see cref="ClassDeclarationSyntax" /> instances.
	/// </summary>
	public static class ClassDeclarationExtensions
	{
		/// <summary>
		///     Generates a compilation unit containing a part of the partial <paramref name="classDeclaration" /> containing the
		///     <paramref name="members" />.
		/// </summary>
		/// <param name="classDeclaration">The class declaration the part should be declared for.</param>
		/// <param name="semanticModel">
		///     The semantic model that should be used to resolve the type symbol of the <paramref name="classDeclaration" />.
		/// </param>
		/// <param name="members">The members that should be added to the class.</param>
		[Pure, NotNull]
		public static CompilationUnitSyntax GeneratePartWithMembers([NotNull] this ClassDeclarationSyntax classDeclaration,
																	[NotNull] SemanticModel semanticModel,
																	[NotNull] IEnumerable<MemberDeclarationSyntax> members)
		{
			Requires.NotNull(classDeclaration, () => classDeclaration);
			Requires.NotNull(members, () => members);
			Requires.NotNull(semanticModel, () => semanticModel);
			Requires.That(classDeclaration.Modifiers.Any(SyntaxKind.PartialKeyword), "Expected the class to be declared as 'partial'.");

			var symbol = classDeclaration.GetTypeSymbol(semanticModel);
			var generatedClass = SyntaxFactory
				.ClassDeclaration(classDeclaration.Identifier)
				.WithTypeParameterList(classDeclaration.TypeParameterList)
				.WithMembers(SyntaxFactory.List(members))
				.WithModifiers(SyntaxFactory.TokenList(SyntaxFactory.Token(SyntaxKind.PartialKeyword)));

			CompilationUnitSyntax compilationUnit;

			if (symbol.ContainingType != null)
			{
				generatedClass = SyntaxFactory
					.ClassDeclaration(symbol.ContainingType.Name)
					.WithTypeParameterList(classDeclaration.Ancestors().OfType<ClassDeclarationSyntax>().First().TypeParameterList)
					.WithMembers(SyntaxFactory.SingletonList((MemberDeclarationSyntax)generatedClass))
					.WithModifiers(SyntaxFactory.TokenList(SyntaxFactory.Token(SyntaxKind.PartialKeyword)));
			}

			if (symbol.ContainingNamespace != null && !symbol.ContainingNamespace.IsGlobalNamespace)
			{
				var namespaceName = SyntaxFactory.ParseName(symbol.ContainingNamespace.ToDisplayString());
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

			return compilationUnit;
		}
	}
}