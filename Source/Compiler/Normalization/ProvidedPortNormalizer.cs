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
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;

	/// <summary>
	///     Ensures that all provided ports are marked with the <see cref="ProvidedAttribute" />.
	/// 
	///     For instance:
	///     <code>
	///    		public void MyMethod(int a, double b) { ... }
	///    		// becomes:
	///    		[SafetySharp.Modeling.ProvidedAttribute] public void MyMethod(int a, double b) { ... }
	///    		
	///    		public int MyProperty { get; set; } // TODO!
	///    		// becomes:
	///    		public int MyProperty { [SafetySharp.Modeling.ProvidedAttribute] get; [SafetySharp.Modeling.ProvidedAttribute] set; }
	///   	</code>
	/// </summary>
	public class ProvidedPortNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     Represents the [Provided] attribute syntax.
		/// </summary>
		private static readonly AttributeListSyntax ProvidedAttribute = 
			SyntaxBuilder.Attribute(typeof(ProvidedAttribute).FullName).WithTrailingSpace();

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public ProvidedPortNormalizer()
			: base(NormalizationScope.Components)
		{
		}

		/// <summary>
		///     Adds the <see cref="ProvidedAttribute" />, if necessary.
		/// </summary>
		public override SyntaxNode VisitMethodDeclaration(MethodDeclarationSyntax methodDeclaration)
		{
			if (methodDeclaration.HasAttribute<ProvidedAttribute>(SemanticModel) || methodDeclaration.Modifiers.Any(SyntaxKind.ExternKeyword))
				return methodDeclaration;

			return methodDeclaration.WithAttributeLists(methodDeclaration.AttributeLists.Add(ProvidedAttribute));
		}
	}
}