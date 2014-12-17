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

namespace SafetySharp.CSharpCompiler.Normalization
{
	using System;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Roslyn;
	using Roslyn.Syntax;

	/// <summary>
	///     Replaces all property declarations with expression bodies with regular getter-only property declarations.
	/// 
	///     For instance:
	///     <code>
	///     	public int X => 1;
	///     	// becomes:
	///     	public int X { get { return 1; } }
	///     	
	///     	[A] bool I.X => false;
	///     	// becomes:
	///     	[A] bool I.X { get { return false; } }
	///    	</code>
	/// </summary>
	public class ExpressionPropertyNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public ExpressionPropertyNormalizer()
			: base(NormalizationScope.Components)
		{
		}

		/// <summary>
		///     Ensures that the <paramref name="classDeclaration" /> is only normalized when the normalizer has the appropriate
		///     <see cref="NormalizationScope" />.
		/// </summary>
		public override SyntaxNode VisitClassDeclaration(ClassDeclarationSyntax classDeclaration)
		{
			if (!ShouldNormalizeClassDeclaration(classDeclaration))
				return classDeclaration;

			foreach (var propertyDeclaration in classDeclaration.Descendants<PropertyDeclarationSyntax>())
				classDeclaration = NormalizeProperty(classDeclaration, propertyDeclaration);

			return classDeclaration;
		}

		/// <summary>
		///     Replaces <paramref name="propertyDeclaration" />'s expressino body with a getter.
		/// </summary>
		/// <param name="classDeclaration">The class declaration the <paramref name="propertyDeclaration" /> belongs to.</param>
		/// <param name="propertyDeclaration">The property declaration that should be normalized.</param>
		private static ClassDeclarationSyntax NormalizeProperty(ClassDeclarationSyntax classDeclaration,
																PropertyDeclarationSyntax propertyDeclaration)
		{
			// Nothing to do here for properties without expression bodies
			if (propertyDeclaration.ExpressionBody == null)
				return classDeclaration;

			var members = classDeclaration.Members;
			members = members.Remove(propertyDeclaration);

			var returnStatement = SyntaxFactory.ReturnStatement(propertyDeclaration.ExpressionBody.Expression).NormalizeWhitespace();
			var getterBlock = SyntaxFactory.Block(returnStatement.WithLeadingAndTrailingSpace()).WithLeadingAndTrailingSpace();
			var getter = SyntaxFactory.AccessorDeclaration(SyntaxKind.GetAccessorDeclaration, getterBlock).WithLeadingAndTrailingSpace();
			var accessors = SyntaxFactory.AccessorList(SyntaxFactory.List(new[] { getter }));

			propertyDeclaration = propertyDeclaration.WithSemicolon(default(SyntaxToken)).WithExpressionBody(null).WithAccessorList(accessors);
			propertyDeclaration = propertyDeclaration.WithTrailingSpace();

			members = members.Add(propertyDeclaration);
			return classDeclaration.WithMembers(members);
		}
	}
}