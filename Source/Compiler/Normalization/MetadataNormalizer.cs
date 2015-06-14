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
	public sealed class MetadataNormalizer : SymbolNormalizer
	{
		/// <summary>
		///     The name of the builder variable.
		/// </summary>
		private const string BuilderVariableName = "builder";

		/// <summary>
		///     The name of the metadata initialization method.
		/// </summary>
		private readonly string _metadataMethod = "InitializeMetadata".ToSynthesized();

		/// <summary>
		///     Normalizes the <paramref name="typeSymbol" />.
		/// </summary>
		/// <param name="typeSymbol">The type symbol that should be normalized.</param>
		protected override void NormalizeTypeSymbol(INamedTypeSymbol typeSymbol)
		{
			if (typeSymbol.IsDerivedFromComponent(Compilation))
				GenerateComponentMetadata(typeSymbol);
		}

		/// <summary>
		///     Generates the metadata initialization code for the component <paramref name="type" />.
		/// </summary>
		/// <param name="type">The component type the code should be generated for.</param>
		private void GenerateComponentMetadata(INamedTypeSymbol type)
		{
			var members = GetFieldMetadata(type)
				.Union(GetRequiredPortMetadata(type))
				.Union(GetProvidedPortMetadata(type))
				.Union(GetUpdateMethodMetadata(type))
				.Union(GetFaultMetadata(type));

			GenerateMetadataMethod(type, members);
		}

		/// <summary>
		///     Generates the method that initializes the type's metadata.
		/// </summary>
		/// <param name="type">The type the code should be generated for.</param>
		/// <param name="statements">The statements that should be executed by the method.</param>
		private void GenerateMetadataMethod(INamedTypeSymbol type, IEnumerable<StatementSyntax> statements)
		{
			var buildersType = Syntax.TypeExpression(Compilation.GetTypeSymbol(typeof(MetadataBuilders)));
			var getBuilder = Syntax.MemberAccessExpression(buildersType, "GetBuilder");
			var builderInitializer = Syntax.InvocationExpression(getBuilder, Syntax.ThisExpression());
			var builderDeclaration = Syntax.LocalDeclarationStatement(BuilderVariableName, builderInitializer).NormalizeWhitespace();

			var methodDeclaration = Syntax.MethodDeclaration(
				name: _metadataMethod,
				accessibility: Accessibility.Private,
				statements: new[] { builderDeclaration }.Concat(statements));

			AddMembers(type, (MethodDeclarationSyntax)methodDeclaration);

			var attribute = Syntax.Attribute(typeof(MetadataAttribute).FullName, Syntax.LiteralExpression(_metadataMethod));
			AddAttributes(type, (AttributeListSyntax)attribute);
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
					if (field.IsConst)
						return false;

					switch (field.Type.SpecialType)
					{
						case SpecialType.System_Boolean:
						case SpecialType.System_Int32:
						case SpecialType.System_Double:
							return true;
						default:
							return field.Type.TypeKind == TypeKind.TypeParameter || field.Type.TypeKind == TypeKind.Enum;
					}
				});

			foreach (var field in fields)
			{
				var fieldInfo = field.GetRuntimeFieldExpression(Compilation, Syntax);
				var methodName = field.Type.TypeKind == TypeKind.TypeParameter ? "WithGenericField" : "WithField";
				var withFieldMethod = Syntax.MemberAccessExpression(Syntax.IdentifierName(BuilderVariableName), methodName);
				var invocation = Syntax.InvocationExpression(withFieldMethod, fieldInfo);
				yield return (StatementSyntax)Syntax.ExpressionStatement(invocation).NormalizeWhitespace().WithTrailingNewLines(1);
			}
		}

		/// <summary>
		///     Generates the metadata initialization code for all required ports of the <paramref name="type" />.
		/// </summary>
		/// <param name="type">The type that declares the required ports the metadata initialization code should be generated for.</param>
		private IEnumerable<StatementSyntax> GetRequiredPortMetadata(INamedTypeSymbol type)
		{
			var methods = type
				.GetMembers()
				.OfType<IMethodSymbol>()
				.Where(method => method.IsRequiredPort(Compilation));

			foreach (var method in methods)
			{
				var withRequiredPortMethod = Syntax.MemberAccessExpression(Syntax.IdentifierName(BuilderVariableName), "WithRequiredPort");
				var invocation = Syntax.InvocationExpression(withRequiredPortMethod, GetMethodInfo(method));
				yield return (StatementSyntax)Syntax.ExpressionStatement(invocation).NormalizeWhitespace().WithTrailingNewLines(1);
			}
		}

		/// <summary>
		///     Generates the metadata initialization code for all provided ports of the <paramref name="type" />.
		/// </summary>
		/// <param name="type">The type that declares the provided ports the metadata initialization code should be generated for.</param>
		private IEnumerable<StatementSyntax> GetProvidedPortMetadata(INamedTypeSymbol type)
		{
			var methods = type
				.GetMembers()
				.OfType<IMethodSymbol>()
				.Where(method => method.IsProvidedPort(Compilation) && !method.IsAbstract);

			foreach (var method in methods)
			{
				var withProvidedPort = Syntax.MemberAccessExpression(Syntax.IdentifierName(BuilderVariableName), "WithProvidedPort");
				var port = GetMethodInfo(method);

				var invocation = method.OverriddenMethod == null || method.OverriddenMethod.IsAbstract
					? Syntax.InvocationExpression(withProvidedPort, port)
					: Syntax.InvocationExpression(withProvidedPort, port, GetMethodInfo(method.OverriddenMethod));

				yield return (StatementSyntax)Syntax.ExpressionStatement(invocation).NormalizeWhitespace().WithTrailingNewLines(1);
			}
		}

		/// <summary>
		///     Generates the metadata initialization code for the Update method of the <paramref name="type" />.
		/// </summary>
		/// <param name="type">The type that declares the Update method the metadata initialization code should be generated for.</param>
		private IEnumerable<StatementSyntax> GetUpdateMethodMetadata(INamedTypeSymbol type)
		{
			var methods = type
				.GetMembers()
				.OfType<IMethodSymbol>()
				.Where(method => method.IsUpdateMethod(Compilation));

			foreach (var method in methods)
			{
				var withStepMethod = Syntax.MemberAccessExpression(Syntax.IdentifierName(BuilderVariableName), "WithStepMethod");
				var overridingMethod = GetMethodInfo(method);
				var overriddenMethod = GetMethodInfo(method.OverriddenMethod);
				var invocation = Syntax.InvocationExpression(withStepMethod, overridingMethod, overriddenMethod);
				yield return (StatementSyntax)Syntax.ExpressionStatement(invocation).NormalizeWhitespace().WithTrailingNewLines(1);
			}
		}

		/// <summary>
		///     Generates the metadata initialization code for faults affecting the <paramref name="type" />.
		/// </summary>
		/// <param name="type">The type that declares the faults the metadata initialization code should be generated for.</param>
		private IEnumerable<StatementSyntax> GetFaultMetadata(INamedTypeSymbol type)
		{
			var faults = type
				.GetMembers()
				.OfType<INamedTypeSymbol>()
				.Where(fault => fault.IsDerivedFromFault(Compilation));

			foreach (var fault in faults)
			{
				var withFault = Syntax.MemberAccessExpression(Syntax.IdentifierName(BuilderVariableName), "WithFault");
				var faultCreationExpression = Syntax.ObjectCreationExpression(fault);
				var invocation = Syntax.InvocationExpression(withFault, faultCreationExpression);
				yield return (StatementSyntax)Syntax.ExpressionStatement(invocation).NormalizeWhitespace().WithTrailingNewLines(1);
			}
		}

		/// <summary>
		///     Gets the <see cref="ReflectionHelpers.GetMethod" /> invocation that gets the <paramref name="method" /> using
		///     reflection.
		/// </summary>
		/// <param name="method">The method the code should be created for.</param>
		private ExpressionSyntax GetMethodInfo(IMethodSymbol method)
		{
			var declaringTypeArg = SyntaxFactory.TypeOfExpression((TypeSyntax)Syntax.TypeExpression(method.ContainingType));
			var parameters = GetParameterTypeArray(method);
			var returnType = SyntaxFactory.TypeOfExpression((TypeSyntax)Syntax.TypeExpression(method.ReturnType));
			var nameArg = Syntax.LiteralExpression(method.Name);
			var reflectionHelpersType = Syntax.TypeExpression(Compilation.GetTypeSymbol(typeof(ReflectionHelpers)));
			var getMethodMethod = Syntax.MemberAccessExpression(reflectionHelpersType, "GetMethod");
			return (ExpressionSyntax)Syntax.InvocationExpression(getMethodMethod, declaringTypeArg, nameArg, parameters, returnType);
		}

		/// <summary>
		///     Gets the parameter type array that can be used to retrieve the <paramref name="method" /> via reflection.
		/// </summary>
		/// <param name="method">The method the parameter type array should be returned for.</param>
		private ExpressionSyntax GetParameterTypeArray(IMethodSymbol method)
		{
			var typeExpressions = method.Parameters.Select(p =>
			{
				var typeofExpression = SyntaxFactory.TypeOfExpression((TypeSyntax)Syntax.TypeExpression(p.Type));
				if (p.RefKind == RefKind.None)
					return typeofExpression;

				var makeRefType = Syntax.MemberAccessExpression(typeofExpression, "MakeByRefType");
				return (ExpressionSyntax)Syntax.InvocationExpression(makeRefType);
			});

			var arguments = SyntaxFactory.SeparatedList(typeExpressions);
			var initialize = SyntaxFactory.InitializerExpression(SyntaxKind.ArrayInitializerExpression, arguments);
			var arrayType = Syntax.ArrayTypeExpression(Syntax.TypeExpression(Compilation.GetTypeSymbol<Type>()));
			return SyntaxFactory.ArrayCreationExpression((ArrayTypeSyntax)arrayType, initialize);
		}
	}
}