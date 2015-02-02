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
	using System.Diagnostics;
	using System.Linq;
	using System.Runtime.CompilerServices;
	using CSharp.Roslyn;
	using CSharp.Roslyn.Symbols;
	using CSharp.Roslyn.Syntax;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;

	/// <summary>
	///     Replaces all extern method declarations within a component with a matching delegate type, a field of that
	///     delegate type, and a non-extern method invoking the delegate instance stored in the field.
	/// 
	///     For instance:
	///     <code>
	///    		public extern void MyMethod(int a, double b);
	///    		// becomes (on a single line with uniquely generated names):
	///  		[CompilerGenerated] public delegate void d(int a, double b);
	///  		[DebuggerBrowsable(DebuggerBrowsableState.Never), CompilerGenerated] d f;
	///    		[SafetySharp.Modeling.RequiredAttribute] public void MyMethod(int a, double b) { f(a, b); }
	///    		
	///    		private extern bool MyMethod(out int a);
	///    		// becomes (on a single line with uniquely generated names):
	///    		[CompilerGenerated] public delegate bool d(out int a);
	///  		[DebuggerBrowsable(DebuggerBrowsableState.Never), CompilerGenerated] private d f;
	///    		[SafetySharp.Modeling.RequiredAttribute] private bool MyMethod(out int a) { return f(out a); }
	///  
	/// 		private extern bool MyProperty { get; set; } // TODO!
	///    		// becomes (on a single line with uniquely generated names):
	///    		[CompilerGenerated] public delegate bool d1();
	///   		[CompilerGenerated] public delegate void d2(bool value);
	///  		[DebuggerBrowsable(DebuggerBrowsableState.Never), CompilerGenerated] private d1 f1;
	///  		[DebuggerBrowsable(DebuggerBrowsableState.Never), CompilerGenerated] private d2 f2;
	///    		private bool MyProperty { [SafetySharp.Modeling.RequiredAttribute] get { return f1(); } [SafetySharp.Modeling.RequiredAttribute] set { f2(value); } }
	///   	</code>
	/// </summary>
	public class RequiredPortNormalizer : Normalizer
	{
		/// <summary>
		///     Represents the [CompilerGenerated] attribute syntax.
		/// </summary>
		private static readonly AttributeListSyntax CompilerGeneratedAttribute =
			SyntaxBuilder.Attribute(typeof(CompilerGeneratedAttribute).FullName).WithTrailingSpace();

		/// <summary>
		///     Represents the [Required] attribute syntax.
		/// </summary>
		private static readonly AttributeListSyntax RequiredAttribute = SyntaxBuilder.Attribute(typeof(RequiredAttribute).FullName);

		/// <summary>
		///     Represents the [DebuggerBrowsable(DebuggerBrowsableState.Never)] attribute syntax.
		/// </summary>
		private static readonly AttributeListSyntax BrowsableAttribute = SyntaxBuilder.Attribute(
			typeof(DebuggerBrowsableAttribute).FullName,
			SyntaxFactory.ParseExpression("System.Diagnostics.DebuggerBrowsableState.Never"));

		/// <summary>
		///     The number of required ports declared by the compilation.
		/// </summary>
		private int _portCount;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public RequiredPortNormalizer()
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
				if (method != null && method.Modifiers.Any(SyntaxKind.ExternKeyword))
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
			var methodDelegate = methodSymbol.GetSynthesizedDelegateDeclaration("ReqPortDelegate" + _portCount);
			methodDelegate = methodDelegate.AddAttributeLists(CompilerGeneratedAttribute);

			// Create the field
			var fieldName = IdentifierNameSynthesizer.ToSynthesizedName("reqPortField" + _portCount++);
			var field = SyntaxBuilder.Field(fieldName, methodDelegate.Identifier.ValueText, Visibility.Private, BrowsableAttribute);
			field = field.AddAttributeLists(CompilerGeneratedAttribute).AsSingleLine();

			// Add the [Required] attribute if it is not already present
			var originalDeclaration = methodDeclaration;
			if (!methodDeclaration.HasAttribute<RequiredAttribute>(SemanticModel))
				methodDeclaration = methodDeclaration.WithAttributeLists(methodDeclaration.AttributeLists.Add(RequiredAttribute));

			// Remove the 'extern' keyword from the method
			var externIndex = methodDeclaration.Modifiers.IndexOf(SyntaxKind.ExternKeyword);
			methodDeclaration = methodDeclaration.WithModifiers(methodDeclaration.Modifiers.RemoveAt(externIndex));

			// Invoke the delegate stored in the field
			var fieldReference = SyntaxFactory.ParseExpression("this." + fieldName);
			var arguments = methodDeclaration.ParameterList.Parameters.Select(parameter =>
			{
				var argument = SyntaxFactory.Argument(SyntaxFactory.IdentifierName(parameter.Identifier));

				if (parameter.Modifiers.IndexOf(SyntaxKind.RefKeyword) != -1)
					return argument.WithRefOrOutKeyword(SyntaxFactory.Token(SyntaxKind.RefKeyword));

				if (parameter.Modifiers.IndexOf(SyntaxKind.OutKeyword) != -1)
					return argument.WithRefOrOutKeyword(SyntaxFactory.Token(SyntaxKind.OutKeyword));

				return argument;
			});

			var argumentList = SyntaxFactory.SeparatedList(arguments);
			var body = SyntaxFactory.InvocationExpression(fieldReference, SyntaxFactory.ArgumentList(argumentList));
			var arrowExpression = SyntaxFactory.ArrowExpressionClause(body);
			methodDeclaration = methodDeclaration.WithExpressionBody(arrowExpression);
			methodDeclaration = methodDeclaration.NormalizeWhitespace().AsSingleLine().EnsureSameLineCount(originalDeclaration);

			// Now add the delegate, field, and modified method to the members collection, 
			// removing the original method declaration
			members = members.RemoveAt(index);
			members = members.Insert(index, methodDelegate);
			members = members.Insert(++index, field);
			members = members.Insert(++index, methodDeclaration);
		}
	}
}