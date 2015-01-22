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

namespace SafetySharp.CSharpCompiler.Normalization
{
	using System;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Roslyn;
	using Roslyn.Syntax;

	/// <summary>
	///     Replaces all method declarations with expression bodies with regular method declarations.
	/// 
	///     For instance:
	///     <code>
	///     	public int X() => 1;
	///     	// becomes:
	///     	public int X() { return 1; }
	///     	
	///     	[A] bool I.X(bool b) => !b;
	///     	// becomes:
	///     	[A] bool I.X(bool b) { return !b; }
	///    	</code>
	/// </summary>
	public class ExpressionMethodNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public ExpressionMethodNormalizer()
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

			foreach (var methodDeclaration in classDeclaration.Descendants<MethodDeclarationSyntax>())
				classDeclaration = NormalizeMethod(classDeclaration, methodDeclaration);

			return classDeclaration;
		}

		/// <summary>
		///     Replaces <paramref name="methodDeclaration" />'s expression body with a regular method body.
		/// </summary>
		/// <param name="classDeclaration">The class declaration the <paramref name="methodDeclaration" /> belongs to.</param>
		/// <param name="methodDeclaration">The method declaration that should be normalized.</param>
		private static ClassDeclarationSyntax NormalizeMethod(ClassDeclarationSyntax classDeclaration, MethodDeclarationSyntax methodDeclaration)
		{
			// Nothing to do here for methods without expression bodies
			if (methodDeclaration.ExpressionBody == null)
				return classDeclaration;

			var members = classDeclaration.Members;
			members = members.Remove(methodDeclaration);

			var returnStatement = SyntaxFactory.ReturnStatement(methodDeclaration.ExpressionBody.Expression).NormalizeWhitespace();
			var body = SyntaxFactory.Block(returnStatement.WithLeadingAndTrailingSpace()).WithTrailingSpace();

			methodDeclaration = methodDeclaration.WithSemicolonToken(default(SyntaxToken)).WithExpressionBody(null).WithBody(body);
			methodDeclaration = methodDeclaration.WithTrailingSpace();

			members = members.Add(methodDeclaration);
			return classDeclaration.WithMembers(members);
		}
	}
}