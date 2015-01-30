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
	using CSharp.Roslyn.Symbols;
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
	///    		// becomes (on a single line with uniquely generated names):
	///  		public delegate void d(int a, double b);
	///    		[SafetySharp.Modeling.ProvidedAttribute] public void MyMethod(int a, double b) { ... }
	///    		
	///    		public int MyProperty { get; set; } // TODO!
	///    		// becomes (on a single line with uniquely generated names):
	///  		public delegate bool d1();
	///   		public delegate void d2(int value);
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
		///     Normalizes the <paramref name="classDeclaration" />.
		/// </summary>
		protected override ClassDeclarationSyntax NormalizeClassDeclaration(ClassDeclarationSyntax classDeclaration)
		{
			var originalMembers = classDeclaration.Members;
			var members = originalMembers;

			var i = 0;
			foreach (var member in originalMembers)
			{
				var method = member as MethodDeclarationSyntax;
				if (method != null && !method.Modifiers.Any(SyntaxKind.ExternKeyword))
					NormalizeMethod(method, ref members, ref i);
				++i;
			}

			return classDeclaration.WithMembers(members);
		}

		/// <summary>
		///     Normalizes the given method declaration and adds the generated members to the member list at the given index.
		/// </summary>
		/// <param name="methodDeclaration">The method declaration that should be normalized.</param>
		/// <param name="members">The members of the containing type that should be updated.</param>
		/// <param name="index">The index where the generated members should be inserted.</param>
		private void NormalizeMethod(MethodDeclarationSyntax methodDeclaration,
									 ref SyntaxList<MemberDeclarationSyntax> members,
									 ref int index)
		{
			// Create the delegate
			var methodSymbol = methodDeclaration.GetMethodSymbol(SemanticModel);
			var methodDelegate = methodSymbol.GetSynthesizedDelegateDeclaration();

			// Add the [Provided] attribute if it is not already present
			if (!methodDeclaration.HasAttribute<ProvidedAttribute>(SemanticModel))
				methodDeclaration = methodDeclaration.WithAttributeLists(methodDeclaration.AttributeLists.Add(ProvidedAttribute));

			// Now add the delegate and modified method to the members collection, 
			// removing the original method declaration
			members = members.RemoveAt(index);
			members = members.Insert(index, methodDelegate);
			members = members.Insert(++index, methodDeclaration);
		}
	}
}