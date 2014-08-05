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
	///     Replaces all extern method declarations within a component with a property of the appropriate
	///     delegate type.
	/// 
	///     For instance:
	///     <code>
	///  		public extern void MyMethod(int a, decimal b)
	///  		// becomes:
	///  		public Action{int, decimal} MyMethod { private get; set; }
	///  		
	///  		private extern bool MyMethod(int a)
	///  		// becomes:
	///  		private Func{int, bool} MyMethod { private get; set; }
	/// 	</code>
	/// </summary>
	public class ComponentRequiredPortNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public ComponentRequiredPortNormalizer()
			: base(NormalizationScope.Components)
		{
		}

		/// <summary>
		///     Normalizes required port component class methods.
		/// </summary>
		/// <param name="methodDeclaration">The method declaration that should be normalized.</param>
		public override SyntaxNode VisitMethodDeclaration(MethodDeclarationSyntax methodDeclaration)
		{
			if (!methodDeclaration.Modifiers.Any(SyntaxKind.ExternKeyword))
				return methodDeclaration;

			var propertyType = methodDeclaration.GetDelegateType(SemanticModel);
			var getterVisibility = methodDeclaration.GetVisibility() == Visibility.Private ? (Visibility?)null : Visibility.Private;
			var property = SyntaxBuilder.AutoProperty(methodDeclaration.Identifier.ValueText, propertyType,
				methodDeclaration.GetVisibility(), getterVisibility, null);

			if (methodDeclaration.ExplicitInterfaceSpecifier != null)
				property = property.WithExplicitInterfaceSpecifier(methodDeclaration.ExplicitInterfaceSpecifier)
								   .WithModifiers(new SyntaxTokenList());

			if (methodDeclaration.AttributeLists.Count != 0)
				property = property.WithAttributeLists(methodDeclaration.AttributeLists);

			return property.AsSingleLine().WithTrivia(methodDeclaration).EnsureSameLineCount(methodDeclaration);
		}
	}
}