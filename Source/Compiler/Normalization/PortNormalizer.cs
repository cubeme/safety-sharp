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
	///     Replaces all port declarations within a component with a matching delegate type, a field of that
	///     delegate type, and a non-extern method invoking the delegate instance stored in the field.
	/// 
	///     For instance:
	///     <code>
	///    		public extern void MyMethod(int a, double b);
	///    		// becomes (on a single line with uniquely generated names):
	///  		[CompilerGenerated] public delegate void d(int a, double b);
	///  		[DebuggerBrowsable(DebuggerBrowsableState.Never), CompilerGenerated] d f;
	///    		[SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute("f")] public void MyMethod(int a, double b) { f(a, b); }
	///    		
	///    		private extern bool MyMethod(out int a);
	///    		// becomes (on a single line with uniquely generated names):
	///    		[CompilerGenerated] public delegate bool d(out int a);
	///  		[DebuggerBrowsable(DebuggerBrowsableState.Never), CompilerGenerated] private d f;
	///    		[SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute("f")] private bool MyMethod(out int a) { return f(out a); }
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
	///         [CompilerGenerated] public delegate void d(int a, double b);
	///  		[DebuggerBrowsable(DebuggerBrowsableState.Never), CompilerGenerated] d f;
	///         private void __MyMethod__(int a, double b) { ... }
	///    		[SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.BackingFieldAttribute("f")] public void MyMethod(int a, double b) { f(a, b); }
	///   	</code>
	/// </summary>
	public class PortNormalizer : Normalizer
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
		///     The number of required ports declared by the compilation.
		/// </summary>
		private int _portCount;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public PortNormalizer()
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

				if (method != null && method.Modifiers.IndexOf(SyntaxKind.StaticKeyword) == -1)
				{
					if (method.Modifiers.Any(SyntaxKind.ExternKeyword))
						NormalizeRequiredPort(method, ref members, ref i);
					else
						NormalizeProvidedPort(method, ref members, ref i);

					++_portCount;
				}

				++i;
			}

			return classDeclaration.WithMembers(members);
		}

		/// <summary>
		///     Normalizes the given required port declaration and adds the generated members to the member list at the given index.
		/// </summary>
		/// <param name="methodDeclaration">The method declaration that should be normalized.</param>
		/// <param name="members">The members of the containing type that should be updated.</param>
		/// <param name="index">The index where the generated members should be inserted.</param>
		private void NormalizeRequiredPort(MethodDeclarationSyntax methodDeclaration,
										   ref SyntaxList<MemberDeclarationSyntax> members,
										   ref int index)
		{
			var originalDeclaration = methodDeclaration;
			var methodDelegate = CreateDelegate(methodDeclaration);
			var methodField = CreateField(methodDelegate);

			// Add the [Required] attribute if it is not already present
			if (!methodDeclaration.HasAttribute<RequiredAttribute>(SemanticModel))
				methodDeclaration = methodDeclaration.WithAttributeLists(methodDeclaration.AttributeLists.Add(RequiredAttribute.WithTrailingSpace()));

			// Remove the 'extern' keyword from the method
			var externIndex = methodDeclaration.Modifiers.IndexOf(SyntaxKind.ExternKeyword);
			methodDeclaration = methodDeclaration.WithModifiers(methodDeclaration.Modifiers.RemoveAt(externIndex));

			// Replace the method's body and ensure that we don't modify the line count of the containing type
			methodDeclaration = AddBackingFieldAttribute(methodDeclaration);
			methodDeclaration = ReplaceBodyWithDelegateInvocation(methodDeclaration);
			methodDeclaration = methodDeclaration.RemoveComments();
			methodDeclaration = methodDeclaration.NormalizeWhitespace().AsSingleLine().WithLeadingTrivia(originalDeclaration.GetLeadingTrivia());
			methodDeclaration = methodDeclaration.EnsureSameLineCount(originalDeclaration);

			UpdateMemberDeclarations(ref members, ref index, methodDeclaration, methodField, methodDelegate);
		}

		/// <summary>
		///     Normalizes the given provided port declaration and adds the generated members to the member list at the given index.
		/// </summary>
		/// <param name="methodDeclaration">The method declaration that should be normalized.</param>
		/// <param name="members">The members of the containing type that should be updated.</param>
		/// <param name="index">The index where the generated members should be inserted.</param>
		private void NormalizeProvidedPort(MethodDeclarationSyntax methodDeclaration,
										   ref SyntaxList<MemberDeclarationSyntax> members,
										   ref int index)
		{
			// Don't normalize the update method
			if (methodDeclaration.GetMethodSymbol(SemanticModel).IsUpdateMethod(SemanticModel))
				return;

			var originalDeclaration = methodDeclaration;
			var methodDelegate = CreateDelegate(methodDeclaration);
			var methodField = CreateField(methodDelegate);

			// Create the private port implementation method
			var prefix = originalDeclaration.ExplicitInterfaceSpecifier != null
				? originalDeclaration.ExplicitInterfaceSpecifier.ToString().Replace(".", "_").Replace("<", "_").Replace(">", "_")
				: String.Empty;
			var methodName = prefix + originalDeclaration.Identifier.Text;
			var portImplementationName = SyntaxFactory.Identifier(IdentifierNameSynthesizer.ToSynthesizedName(methodName));
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
				UpdateMemberDeclarations(ref members, ref index, methodDeclaration);
			else
			{
				methodDeclaration = AddBackingFieldAttribute(methodDeclaration);
				methodDeclaration = ReplaceBodyWithDelegateInvocation(methodDeclaration);
				methodDeclaration = methodDeclaration.RemoveComments();
				methodDeclaration = methodDeclaration.NormalizeWhitespace().AsSingleLine();

				UpdateMemberDeclarations(ref members, ref index, methodDeclaration, methodField, methodDelegate, portImplementation);
			}
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

			methodDeclaration = methodDeclaration.WithBody(null).WithExpressionBody(arrowExpression);

			if (methodDeclaration.SemicolonToken.Kind() != SyntaxKind.SemicolonToken)
				return methodDeclaration.WithSemicolonToken(SyntaxFactory.Token(SyntaxKind.SemicolonToken));

			return methodDeclaration;
		}

		/// <summary>
		///     Adds <paramref name="newMembers" /> to the list of <paramref name="members" /> at the given <paramref name="index" />.
		/// </summary>
		/// <param name="members">The members of the containing type that should be updated.</param>
		/// <param name="index">The index where the new members should be inserted.</param>
		/// <param name="newMembers">The new members that should be added.</param>
		private void UpdateMemberDeclarations(ref SyntaxList<MemberDeclarationSyntax> members,
											  ref int index,
											  params MemberDeclarationSyntax[] newMembers)
		{
			members = members.RemoveAt(index);

			foreach (var newMember in newMembers)
				members = members.Insert(index, newMember);

			index += newMembers.Length - 1;
		}
	}
}