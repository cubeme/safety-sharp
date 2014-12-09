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
	using Utilities;

	/// <summary>
	///     Replaces all property declarations with getter and setter method declarations within component classes or interfaces.
	///     Assumes that there are no auto-properties or properties with expression bodies. Property reads and writes are updated
	///     accordingly to call the appropriate methods.
	///     Note that this normalizer will create non-compilable C# code if:
	///		- an attribute is applied to a property that cannot be applied to methods as well;
	///		- a property is written and the result value is used again (e.g., x = Prop = 1);
	///		- a property is used in a compound assignment, increment, or decrement expression (e.g., Prop++, Prop += 3);
	/// 
	///     For instance, within component classes:
	///     <code>
	///    		public int X { get { return 1; } }
	///    		// becomes:
	///    		public int __GetX__() { return 1; }
	///    		
	///    		[A] int I.X { [B] get { return 1; } set { Console.WriteLine(value); } }
	///    		// becomes:
	///    		[A] [B] int I.__GetX__() { return 1; }
	///  		[A] void I.__SetX__(int value) { Console.WriteLine(value); }
	///   	</code>
	///     For instance, within component interfaces:
	///     <code>
	///    		int X { get; }
	///    		// becomes:
	///    		int __GetX__();
	///    		
	///    		[A] int X { [B] get; set; }
	///    		// becomes:
	///    		[A] [B] int __GetX__();
	///  		[A] void __SetX__(int value);
	///   	</code>
	/// </summary>
	public class PropertyDeclarationNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public PropertyDeclarationNormalizer()
			: base(NormalizationScope.Components | NormalizationScope.ComponentInterfaces)
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

			return classDeclaration
				.Descendants<PropertyDeclarationSyntax>()
				.Aggregate(classDeclaration, (type, property) => NormalizeProperty(type, property, (members, t) => t.WithMembers(members)));
		}

		/// <summary>
		///     Ensures that the <paramref name="interfaceDeclaration" /> is only normalized when the normalizer has the appropriate
		///     <see cref="NormalizationScope" />.
		/// </summary>
		public override SyntaxNode VisitInterfaceDeclaration(InterfaceDeclarationSyntax interfaceDeclaration)
		{
			if (!ShouldNormalizeInterfaceDeclaration(interfaceDeclaration))
				return interfaceDeclaration;

			return interfaceDeclaration
				.Descendants<PropertyDeclarationSyntax>()
				.Aggregate(interfaceDeclaration, (type, property) => NormalizeProperty(type, property, (members, t) => t.WithMembers(members)));
		}

		/// <summary>
		///     Replaces <paramref name="propertyDeclaration" /> with getter and/or setter methods.
		/// </summary>
		/// <param name="typeDeclaration">The type declaration the <paramref name="propertyDeclaration" /> belongs to.</param>
		/// <param name="propertyDeclaration">The property declaration that should be normalized.</param>
		/// <param name="update">Updates the member's of the <paramref name="typeDeclaration" />.</param>
		private static T NormalizeProperty<T>(T typeDeclaration, PropertyDeclarationSyntax propertyDeclaration,
											  Func<SyntaxList<MemberDeclarationSyntax>, T, T> update)
			where T : TypeDeclarationSyntax
		{
			Assert.IsNull(propertyDeclaration.ExpressionBody, "Unexpected property with expression body.");

			var inInterface = typeof(T) == typeof(InterfaceDeclarationSyntax);
			var attributes = propertyDeclaration.AttributeLists;
			var members = typeDeclaration.Members;
			members = members.Remove(propertyDeclaration);

			foreach (var accessor in propertyDeclaration.AccessorList.Accessors)
			{
				Assert.That(inInterface || accessor.Body != null, "Unexpected auto-implemented property.");

				var accessorType = accessor.CSharpKind();
				var methodAttributes = attributes.AddRange(accessor.AttributeLists);

				Assert.That(accessorType == SyntaxKind.GetAccessorDeclaration || accessorType == SyntaxKind.SetAccessorDeclaration,
					"Expected a get or set accessor declaration.");

				TypeSyntax returnType;
				ParameterListSyntax parameterList;
				string methodName;

				if (accessorType == SyntaxKind.GetAccessorDeclaration)
				{
					returnType = propertyDeclaration.Type;
					parameterList = SyntaxFactory.ParameterList();

					methodName = IdentifierNameSynthesizer.ToSynthesizedName(String.Format("Get{0}", propertyDeclaration.Identifier.ValueText));
				}
				else
				{
					returnType = SyntaxBuilder.VoidType.WithTrailingSpace();

					var parameter = SyntaxFactory.Parameter(SyntaxFactory.Identifier("value")).WithType(propertyDeclaration.Type);
					parameterList = SyntaxFactory.ParameterList(SyntaxFactory.SeparatedList(new[] { parameter }));

					methodName = IdentifierNameSynthesizer.ToSynthesizedName(String.Format("Set{0}", propertyDeclaration.Identifier.ValueText));
				}

				var method = SyntaxFactory.MethodDeclaration(
					attributeLists: methodAttributes,
					modifiers: propertyDeclaration.Modifiers,
					returnType: returnType,
					explicitInterfaceSpecifier: propertyDeclaration.ExplicitInterfaceSpecifier,
					identifier: SyntaxFactory.Identifier(methodName),
					typeParameterList: null,
					parameterList: parameterList,
					constraintClauses: SyntaxFactory.List<TypeParameterConstraintClauseSyntax>(),
					body: accessor.Body == null ? null : accessor.Body.WithLeadingSpace(),
					semicolonToken: inInterface ? SyntaxFactory.Token(SyntaxKind.SemicolonToken).WithTrailingSpace() : default(SyntaxToken));

				members = members.Add(method);
			}

			return update(members, typeDeclaration);
		}

		// TODO: Rewrite usages of property getters and setters
	}
}