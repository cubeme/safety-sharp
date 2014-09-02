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
	///     Replaces all references to enum types with <c>int</c>.
	/// </summary>
	public class EnumTypeNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     The syntax node for the C# integer type.
		/// </summary>
		private readonly TypeSyntax _intType = SyntaxFactory.ParseTypeName("int");

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public EnumTypeNormalizer()
			: base(NormalizationScope.Components)
		{
		}

		/// <summary>
		///     Replaces the <paramref name="nameSyntax" /> with <c>int</c> if it refers to an enumeration type.
		/// </summary>
		/// <param name="nameSyntax">The name syntax that should be replaced.</param>
		private SyntaxNode ReplaceEnumType(NameSyntax nameSyntax)
		{
			var symbol = nameSyntax.GetReferencedSymbol(SemanticModel) as ITypeSymbol;
			if (symbol == null || symbol.TypeKind != TypeKind.Enum)
				return nameSyntax;

			return _intType.WithTrivia(nameSyntax);
		}

		/// <summary>
		///     Replaces the <paramref name="identifier" />, if necessary.
		/// </summary>
		public override SyntaxNode VisitIdentifierName(IdentifierNameSyntax identifier)
		{
			return ReplaceEnumType(identifier);
		}

		/// <summary>
		///     Replaces the <paramref name="name" />, if necessary.
		/// </summary>
		public override SyntaxNode VisitQualifiedName(QualifiedNameSyntax name)
		{
			return ReplaceEnumType(name);
		}

		/// <summary>
		///     Replaces the <paramref name="name" />, if necessary.
		/// </summary>
		public override SyntaxNode VisitAliasQualifiedName(AliasQualifiedNameSyntax name)
		{
			return ReplaceEnumType(name);
		}

		/// <summary>
		///     Ensures that uses of enum literals are not replaced, i.e., we don't want to normalize 'E.A' to 'int.A'.
		/// </summary>
		public override SyntaxNode VisitMemberAccessExpression(MemberAccessExpressionSyntax node)
		{
			return node;
		}
	}
}