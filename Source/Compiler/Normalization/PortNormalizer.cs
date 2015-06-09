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
	using System.Collections.Generic;
	using System.Diagnostics;
	using System.Linq;
	using System.Runtime.CompilerServices;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;

	/// <summary>
	///     Replaces all port declarations within a component with a matching delegate type, a field of that
	///     delegate type, and a non-extern method invoking the delegate instance stored in the field.
	///     For instance:
	///     <code>
	///    		public extern void MyMethod(int a, double b);
	///    		// becomes (on a single line with uniquely generated names):
	///  		[CompilerGenerated] 
	///         private delegate void d(int a, double b);
	///  		[DebuggerBrowsable(DebuggerBrowsableState.Never), CompilerGenerated] 
	///         d f;
	///         [DebuggerHidden]
	///    		[SafetySharp.Modeling.RequiredAttribute()] 
	///         [SafetySharp.Modeling.BackingFieldAttribute("f")] 
	///         public void MyMethod(int a, double b) => f(a, b);
	///    		
	/// 		private extern bool MyProperty { get; set; } // TODO!
	///    		// becomes (on a single line with uniquely generated names):
	///    		[CompilerGenerated] public delegate bool d1();
	///   		[CompilerGenerated] public delegate void d2(bool value);
	///  		[DebuggerBrowsable(DebuggerBrowsableState.Never), CompilerGenerated] private d1 f1;
	///  		[DebuggerBrowsable(DebuggerBrowsableState.Never), CompilerGenerated] private d2 f2;
	///    		private bool MyProperty { [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute("f1")] get { return f1(); } [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute("f2")] set { f2(value); } }
	/// 
	///         public void MyMethod(int a, double b) { ... }
	///    		// becomes:
	///         [CompilerGenerated] 
	///         public delegate void d(int a, double b);
	///  		[DebuggerBrowsable(DebuggerBrowsableState.Never), CompilerGenerated] 
	///         d f;
	///         private void __MyMethod__(int a, double b) { ... }
	///         [DebuggerHidden]
	///    		[SafetySharp.Modeling.ProvidedAttribute()]
	///         [SafetySharp.Modeling.BackingFieldAttribute("f")] 
	///         public void MyMethod(int a, double b) => f(a, b);
	///   	</code>
	/// </summary>
	public sealed class PortNormalizer : Normalizer
	{
		/// <summary>
		///     Represents the [CompilerGenerated] attribute syntax.
		/// </summary>
		private static readonly AttributeListSyntax CompilerGeneratedAttribute =
			SyntaxBuilder.Attribute(typeof(CompilerGeneratedAttribute).FullName).WithTrailingSpace();

		/// <summary>
		///     Represents the [DebuggerHidden] attribute syntax.
		/// </summary>
		private static readonly AttributeListSyntax DebuggerHiddenAttribute =
			SyntaxBuilder.Attribute(typeof(DebuggerHiddenAttribute).FullName).WithTrailingSpace();

		/// <summary>
		///     Represents the [Required] attribute syntax.
		/// </summary>
		private static readonly AttributeListSyntax RequiredAttribute = SyntaxBuilder.Attribute(typeof(RequiredAttribute).FullName);

		/// <summary>
		///     Represents the [Provided] attribute syntax.
		/// </summary>
		private static readonly AttributeListSyntax ProvidedAttribute = SyntaxBuilder.Attribute(typeof(ProvidedAttribute).FullName);

		/// <summary>
		///     Represents the [DebuggerBrowsable(DebuggerBrowsableState.Never)] attribute syntax.
		/// </summary>
		private static readonly AttributeListSyntax BrowsableAttribute = SyntaxBuilder.Attribute(
			typeof(DebuggerBrowsableAttribute).FullName,
			SyntaxFactory.ParseExpression("System.Diagnostics.DebuggerBrowsableState.Never"));

		/// <summary>
		///     The list of members that have been generated during normalization of a class.
		/// </summary>
		private List<MemberDeclarationSyntax> _generatedMembers = new List<MemberDeclarationSyntax>();

		/// <summary>
		///     The number of ports declared by the current component.
		/// </summary>
		private int _portCount;

		/// <summary>
		///     Normalizes the <paramref name="classDeclaration" />.
		/// </summary>
		public override SyntaxNode VisitClassDeclaration(ClassDeclarationSyntax classDeclaration)
		{
			var generatedMembers = _generatedMembers;
			var portCount = _portCount;

			_generatedMembers = new List<MemberDeclarationSyntax>();
			_portCount = 0;

			var normalizedClass = base.VisitClassDeclaration(classDeclaration);

			if (_generatedMembers.Count > 0)
				AddCompilationUnit(classDeclaration.GeneratePartWithMembers(SemanticModel, _generatedMembers));

			_generatedMembers = generatedMembers;
			_portCount = portCount;

			return normalizedClass;
		}

		/// <summary>
		///     Does not normalize ports declared by interfaces.
		/// </summary>
		public override SyntaxNode VisitInterfaceDeclaration(InterfaceDeclarationSyntax interfaceDeclaration)
		{
			return interfaceDeclaration;
		}

		/// <summary>
		///     Normalizes the <paramref name="methodDeclaration" />.
		/// </summary>
		public override SyntaxNode VisitMethodDeclaration(MethodDeclarationSyntax methodDeclaration)
		{
			var methodSymbol = methodDeclaration.GetMethodSymbol(SemanticModel);

			if (methodSymbol.IsRequiredPort(SemanticModel))
				return NormalizeRequiredPort(methodDeclaration);

			if (methodSymbol.IsProvidedPort(SemanticModel))
				return NormalizeProvidedPort(methodDeclaration);

			return methodDeclaration;
		}

		/// <summary>
		///     Normalizes the given required port declaration and adds the generated members to the member list at the given index.
		/// </summary>
		/// <param name="methodDeclaration">The method declaration that should be normalized.</param>
		private MethodDeclarationSyntax NormalizeRequiredPort(MethodDeclarationSyntax methodDeclaration)
		{
			var originalDeclaration = methodDeclaration;

			var methodDelegate = CreateDelegate(methodDeclaration);
			var methodField = CreateField(methodDelegate);

			// Add the [Required] attribute if it is not already present
			if (!methodDeclaration.HasAttribute<RequiredAttribute>(SemanticModel))
			{
				methodDeclaration = methodDeclaration.RemoveTrivia();
				methodDeclaration = methodDeclaration.WithAttributeLists(methodDeclaration.AttributeLists.Add(RequiredAttribute.WithTrailingSpace()));
			}

			// Remove the 'extern' keyword from the method
			var externIndex = methodDeclaration.Modifiers.IndexOf(SyntaxKind.ExternKeyword);
			methodDeclaration = methodDeclaration.WithModifiers(methodDeclaration.Modifiers.RemoveAt(externIndex));

			// Add the [DebuggerHidden] attribute if it is not already present
			if (!originalDeclaration.HasAttribute<DebuggerHiddenAttribute>(SemanticModel))
				methodDeclaration = methodDeclaration.WithAttributeLists(methodDeclaration.AttributeLists.Add(DebuggerHiddenAttribute));

			// Replace the method's body and ensure that we don't modify the line count of the containing type
			methodDeclaration = AddBackingFieldAttribute(methodDeclaration);
			methodDeclaration = ReplaceBodyWithDelegateInvocation(methodDeclaration);
			methodDeclaration = methodDeclaration.NormalizeWhitespace();
			methodDeclaration = methodDeclaration.WithTrivia(originalDeclaration);

			_generatedMembers.Add(methodField);
			_generatedMembers.Add(methodDelegate);

			++_portCount;
			return methodDeclaration.EnsureLineCount(originalDeclaration);
		}

		/// <summary>
		///     Normalizes the given provided port declaration and adds the generated members to the member list at the given index.
		/// </summary>
		/// <param name="methodDeclaration">The method declaration that should be normalized.</param>
		private MethodDeclarationSyntax NormalizeProvidedPort(MethodDeclarationSyntax methodDeclaration)
		{
			var originalDeclaration = methodDeclaration;
			var methodDelegate = CreateDelegate(methodDeclaration);
			var methodField = CreateField(methodDelegate);

			// Create the private port implementation method
			var methodName = IdentifierNameSynthesizer.ToSynthesizedName("DefaultImplementation" + _portCount);
			var portImplementationName = SyntaxFactory.Identifier(methodName).WithTrivia(originalDeclaration.Identifier);
			var portImplementation = originalDeclaration.WithIdentifier(portImplementationName);
			portImplementation = portImplementation.WithAccessibility(Accessibility.Private).WithExplicitInterfaceSpecifier(null);

			// Remove all modifiers from the port implementation except for the 'private' keyword
			var modifiers = portImplementation.Modifiers;
			var privateKeyword = modifiers[modifiers.IndexOf(SyntaxKind.PrivateKeyword)];
			portImplementation = portImplementation.WithModifiers(SyntaxTokenList.Create(privateKeyword));

			// Add the [Provided] attribute if it is not already present
			if (!methodDeclaration.HasAttribute<ProvidedAttribute>(SemanticModel))
				methodDeclaration = methodDeclaration.WithAttributeLists(methodDeclaration.AttributeLists.Add(ProvidedAttribute.WithTrailingSpace()));

			// Replace the method's body and ensure that we don't modify the line count of the containing type
			// We don't change abstract methods, however, except for adding the [Provided] attribute, if necessary
			if (methodDeclaration.Modifiers.IndexOf(SyntaxKind.AbstractKeyword) != -1)
				return methodDeclaration;

			// Add the [DefaultImplementation] attribute
			var implementationArgument = SyntaxFactory.ParseExpression(String.Format("\"{0}\"", methodName));
			var implementationAttribute = SyntaxBuilder.Attribute(typeof(DefaultImplementationAttribute).FullName, implementationArgument);
			methodDeclaration = methodDeclaration.WithAttributeLists(methodDeclaration.AttributeLists.Add(implementationAttribute));

			// Add the [DebuggerHidden] attribute if it is not already present
			if (!originalDeclaration.HasAttribute<DebuggerHiddenAttribute>(SemanticModel))
				methodDeclaration = methodDeclaration.WithAttributeLists(methodDeclaration.AttributeLists.Add(DebuggerHiddenAttribute));

			methodDeclaration = AddBackingFieldAttribute(methodDeclaration);
			methodDeclaration = ReplaceBodyWithDelegateInvocation(methodDeclaration);
			methodDeclaration = methodDeclaration.RemoveComments().WithTrivia(originalDeclaration);

			_generatedMembers.Add(methodField);
			_generatedMembers.Add(methodDelegate);
			_generatedMembers.Add(methodDeclaration);

			++_portCount;
			return portImplementation.EnsureLineCount(originalDeclaration);
		}

		/// <summary>
		///     Gets the name of the delegate for the current port.
		/// </summary>
		private string GetDelegateName()
		{
			return IdentifierNameSynthesizer.ToSynthesizedName("PortDelegate" + _portCount);
		}

		/// <summary>
		///     Gets the name of the field for the current port.
		/// </summary>
		private string GetFieldName()
		{
			return IdentifierNameSynthesizer.ToSynthesizedName("portField" + _portCount);
		}

		/// <summary>
		///     Creates a delegate declaration that is compatible with <paramref name="methodDeclaration" />.
		/// </summary>
		/// <param name="methodDeclaration">The declaration of the method the delegate should be created for.</param>
		private DelegateDeclarationSyntax CreateDelegate(MethodDeclarationSyntax methodDeclaration)
		{
			var methodSymbol = methodDeclaration.GetMethodSymbol(SemanticModel);
			var methodDelegate = methodSymbol.GetSynthesizedDelegateDeclaration(GetDelegateName());
			methodDelegate = methodDelegate.AddAttributeLists(CompilerGeneratedAttribute);

			return methodDelegate;
		}

		/// <summary>
		///     Creates a field declaration that stores <paramref name="methodDelegate" />.
		/// </summary>
		/// <param name="methodDelegate">The delegate the field should be created for.</param>
		private FieldDeclarationSyntax CreateField(DelegateDeclarationSyntax methodDelegate)
		{
			return SyntaxBuilder.Field(GetFieldName(), methodDelegate.Identifier.ValueText, Visibility.Private,
				BrowsableAttribute, CompilerGeneratedAttribute).AsSingleLine();
		}

		/// <summary>
		///     Adds the [BackingField] attribute to <paramref name="methodDeclaration" />.
		/// </summary>
		/// <param name="methodDeclaration">The method declaration the attribute should be added to.</param>
		private MethodDeclarationSyntax AddBackingFieldAttribute(MethodDeclarationSyntax methodDeclaration)
		{
			var backingFieldArgument = SyntaxFactory.ParseExpression(String.Format("\"{0}\"", GetFieldName()));
			var backingFieldAttribute = SyntaxBuilder.Attribute(typeof(BackingFieldAttribute).FullName, backingFieldArgument);

			return methodDeclaration.WithAttributeLists(methodDeclaration.AttributeLists.Add(backingFieldAttribute));
		}

		/// <summary>
		///     Replaces <paramref name="methodDeclaration" />'s body with an invocation of the port's delegate.
		/// </summary>
		/// <param name="methodDeclaration">The method declaration whose body should be replaced.</param>
		private MethodDeclarationSyntax ReplaceBodyWithDelegateInvocation(MethodDeclarationSyntax methodDeclaration)
		{
			var fieldReference = SyntaxFactory.ParseExpression("this." + GetFieldName());
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

			methodDeclaration = methodDeclaration.WithBody(null).WithExpressionBody(arrowExpression.NormalizeWhitespace());

			if (methodDeclaration.SemicolonToken.Kind() != SyntaxKind.SemicolonToken)
				return methodDeclaration.WithSemicolonToken(SyntaxFactory.Token(SyntaxKind.SemicolonToken));

			return methodDeclaration;
		}
	}
}