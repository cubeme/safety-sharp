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
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;

	/// <summary>
	///     Replaces all required port method declarations within a component interface with a property of the appropriate
	///     delegate type.
	/// 
	///     For instance:
	///     <code>
	///   		extern void MyMethod(int a, decimal b) 
	///  		// becomes:
	///   		Action{int, decimal} MyMethod { set; }
	///    
	///   		extern bool MyMethod(int a)
	///   		// becomes:
	///  		Func{int, bool} MyMethod { set; }
	/// 	</code>
	/// </summary>
	public class InterfaceRequiredPortNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public InterfaceRequiredPortNormalizer()
			: base(NormalizationScope.ComponentInterfaces)
		{
		}

		/// <summary>
		///     Normalizes required port component interface methods.
		/// </summary>
		/// <param name="methodDeclaration">The method declaration that should be normalized.</param>
		public override SyntaxNode VisitMethodDeclaration(MethodDeclarationSyntax methodDeclaration)
		{
			if (!methodDeclaration.HasAttribute<RequiredAttribute>(SemanticModel))
				return methodDeclaration;

			var propertyType = methodDeclaration.GetDelegateType(SemanticModel);
			var property = SyntaxBuilder.InterfaceProperty(methodDeclaration.Identifier.ValueText, propertyType, false, true);

			if (methodDeclaration.AttributeLists.Count != 0)
				property = property.WithAttributeLists(methodDeclaration.AttributeLists);

			return property.AsSingleLine().WithTrivia(methodDeclaration).EnsureSameLineCount(methodDeclaration);
		}
	}
}