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
	using System.Linq;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Roslyn;
	using Roslyn.Syntax;

	/// <summary>
	///     Replaces all automatically implemented property declarations with backing fields and a regular property declarations.
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
	public class AutoPropertyNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public AutoPropertyNormalizer()
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
			// Nothing to do here for properties with expression bodies
			if (propertyDeclaration.ExpressionBody != null)
				return classDeclaration;

			// Nothing to do here for properties with only a single accessor
			if (propertyDeclaration.AccessorList.Accessors.Count != 2)
				return classDeclaration;

			var declaredGetter = propertyDeclaration.AccessorList.Accessors.Single(a => a.CSharpKind() == SyntaxKind.GetAccessorDeclaration);
			var declaredSetter = propertyDeclaration.AccessorList.Accessors.Single(a => a.CSharpKind() == SyntaxKind.SetAccessorDeclaration);

			// Nothing to do here for properties with accessors that have a body
			if (declaredGetter.Body != null || declaredSetter.Body != null)
				return classDeclaration;

			var members = classDeclaration.Members;
			members = members.Remove(propertyDeclaration);

			var name = String.Format("BackingField_{0}", propertyDeclaration.Identifier.ValueText);
			if (propertyDeclaration.ExplicitInterfaceSpecifier != null)
				name = String.Format("{0}_{1}", propertyDeclaration.ExplicitInterfaceSpecifier.Name.ToString().Replace(".", "_"), name);

			var fieldName = IdentifierNameSynthesizer.ToSynthesizedName(name);
			var declarator = SyntaxFactory.VariableDeclarator(fieldName);
			var declarators = SyntaxFactory.SingletonSeparatedList(declarator);
			var variable = SyntaxFactory.VariableDeclaration(propertyDeclaration.Type, declarators);
			var modifiers = SyntaxFactory.TokenList(SyntaxFactory.Token(SyntaxKind.PrivateKeyword).WithTrailingSpace());
			var fieldDeclaration = SyntaxFactory.FieldDeclaration(variable).WithModifiers(modifiers).WithTrailingSpace();

			var fieldIdentifier = SyntaxFactory.IdentifierName(fieldName);
			var value = SyntaxFactory.IdentifierName("value");
			var getterBody = SyntaxFactory.ReturnStatement(fieldIdentifier).NormalizeWhitespace().WithLeadingAndTrailingSpace();
			var getterBlock = SyntaxFactory.Block(getterBody).WithLeadingAndTrailingSpace();
			var getter = SyntaxFactory.AccessorDeclaration(SyntaxKind.GetAccessorDeclaration, getterBlock);
			getter = getter.WithAttributeLists(declaredGetter.AttributeLists).WithLeadingSpace();

			var assignment = SyntaxFactory.BinaryExpression(SyntaxKind.SimpleAssignmentExpression, fieldIdentifier, value);
			var setterBody = SyntaxFactory.ExpressionStatement(assignment).NormalizeWhitespace().WithLeadingAndTrailingSpace();
			var setterBlock = SyntaxFactory.Block(setterBody).WithLeadingAndTrailingSpace();
			var setter = SyntaxFactory.AccessorDeclaration(SyntaxKind.SetAccessorDeclaration, setterBlock);
			setter = setter.WithAttributeLists(declaredSetter.AttributeLists).WithTrailingSpace();

			var accessors = SyntaxFactory.AccessorList(SyntaxFactory.List(new[] { getter, setter }));
			propertyDeclaration = propertyDeclaration.WithAccessorList(accessors).WithTrailingSpace();

			members = members.Add(fieldDeclaration);
			members = members.Add(propertyDeclaration);

			return classDeclaration.WithMembers(members);
		}
	}
}