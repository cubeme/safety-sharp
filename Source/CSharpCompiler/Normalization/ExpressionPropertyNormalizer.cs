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
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Roslyn;
	using Roslyn.Syntax;

	/// <summary>
	///     Replaces all property declarations with expression bodies with regular getter-only property declarations.
	/// 
	///     For instance:
	///     <code>
	///     		public int X { get; private set }
	///     		// becomes:
	/// 			int __BackingField_X__;
	///     		public int X { get { return __BackingField_X__; } private set { __BackingField_X__ = value; } }
	///     		
	///     		[A] int I.X { [B] get; set; }
	///     		// becomes:
	/// 			int __I_BackingField_X__;
	///     		[A] int I.X { [B] get { return __I_BackingField_X__; } set { __I_BackingField_X__ = value; } }
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
		///     Replaces <paramref name="propertyDeclaration" /> with a getter and/or setter methods.
		/// </summary>
		/// <param name="classDeclaration">The class declaration the <paramref name="propertyDeclaration" /> belongs to.</param>
		/// <param name="propertyDeclaration">The property declaration that should be normalized.</param>
		private static ClassDeclarationSyntax NormalizeProperty(ClassDeclarationSyntax classDeclaration,
																PropertyDeclarationSyntax propertyDeclaration)
		{
			// Nothing to do here for properties without expression bodies
			if (propertyDeclaration.ExpressionBody == null)
				return classDeclaration;
		}
	}
}