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
	using System.Linq;
	using CompilerServices;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;

	/// <summary>
	///     Adds the metadata initialization code to the various S# types.
	/// </summary>
	public sealed class MetadataNormalizer : Normalizer
	{
		/// <summary>
		///     The name of the builder variable.
		/// </summary>
		private const string BuilderVariableName = "builder";

		/// <summary>
		///     The name of the metadata initialization method.
		/// </summary>
		private const string MetadataMethod = "InitializeMetadata";

		

		/// <summary>
		///     Adds the metadata initialization code to the <paramref name="constructor" />.
		/// </summary>
		public override SyntaxNode VisitConstructorDeclaration(ConstructorDeclarationSyntax constructor)
		{
			var typeSymbol = constructor.GetMethodSymbol(SemanticModel).ContainingType;

			if (!typeSymbol.IsDerivedFromComponent(SemanticModel))
				return base.VisitConstructorDeclaration(constructor);

			GenerateComponentMetadata(typeSymbol);

			constructor = (ConstructorDeclarationSyntax)base.VisitConstructorDeclaration(constructor);
			return constructor; //.WithBody(constructor.Body.WithStatements(statements));
		}

		/// <summary>
		///     Generates the method that initializes the type's metadata.
		/// </summary>
		/// <param name="type">The type the code should be generated for.</param>
		/// <param name="statements">The statements that should be executed by the method.</param>
		private void GenerateMetadataMethod(INamedTypeSymbol type, IEnumerable<StatementSyntax> statements)
		{
			var buildersType = Syntax.TypeExpression(SemanticModel.GetTypeSymbol(typeof(MetadataBuilders)));
			var getBuilder = Syntax.MemberAccessExpression(buildersType, "GetBuilder");
			var builderInitializer = Syntax.InvocationExpression(getBuilder, Syntax.ThisExpression());
			var builderDeclaration = Syntax.LocalDeclarationStatement(BuilderVariableName, builderInitializer).NormalizeWhitespace();

			var methodDeclaration = Syntax.MethodDeclaration(
				name: IdentifierNameSynthesizer.ToSynthesizedName(MetadataMethod),
				accessibility: Accessibility.Private,
				statements: new[] { builderDeclaration }.Concat(statements));

			AddMembers(type, (MethodDeclarationSyntax)methodDeclaration);
		}

		/// <summary>
		///     Generates the metadata initialization code for the component <paramref name="type" />.
		/// </summary>
		/// <param name="type">The component type the code should be generated for.</param>
		private void GenerateComponentMetadata(INamedTypeSymbol type)
		{
			GenerateMetadataMethod(type, GetFieldMetadata(type));
		}

		/// <summary>
		///     Generates the metadata initialization code for all fields of the <paramref name="type" />.
		/// </summary>
		/// <param name="type">The type that declares the fields the metadata initialization code should be generated for.</param>
		private IEnumerable<StatementSyntax> GetFieldMetadata(INamedTypeSymbol type)
		{
			var fields = type
				.GetMembers()
				.OfType<IFieldSymbol>()
				.Where(field =>
				{
					if (field.IsReadOnly || field.IsConst)
						return false;

					switch (field.Type.SpecialType)
					{
						case SpecialType.System_Boolean:
						case SpecialType.System_Int32:
						case SpecialType.System_Double:
							return true;
						default:
							return false;
					}
				});

			foreach (var fieldSymbol in fields)
			{
				var declaringTypeArg = SyntaxFactory.TypeOfExpression((TypeSyntax)Syntax.TypeExpression(type));
				var fieldTypeArg = SyntaxFactory.TypeOfExpression((TypeSyntax)Syntax.TypeExpression(fieldSymbol.Type));
				var nameArg = Syntax.LiteralExpression(fieldSymbol.Name);
				var reflectionHelpersType = Syntax.TypeExpression(SemanticModel.GetTypeSymbol(typeof(ReflectionHelpers)));
				var getFieldMethod = Syntax.MemberAccessExpression(reflectionHelpersType, "GetField");
				var fieldInfo = Syntax.InvocationExpression(getFieldMethod, declaringTypeArg, fieldTypeArg, nameArg);

				var withFieldMethod = Syntax.MemberAccessExpression(Syntax.IdentifierName(BuilderVariableName), "WithField");
				var invocation = Syntax.InvocationExpression(withFieldMethod, fieldInfo);
				yield return (StatementSyntax)Syntax.ExpressionStatement(invocation).NormalizeWhitespace().WithTrailingNewLines(1);
			}
		}
	}
}