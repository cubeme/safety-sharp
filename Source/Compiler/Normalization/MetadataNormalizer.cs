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
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling.Faults;
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

			if (typeSymbol.IsDerivedFrom(Compilation.GetTypeSymbol<OccurrencePattern>()))
				GenerateOccurrencePatternMetadata(typeSymbol);

			if (typeSymbol.IsDerivedFromFault(Compilation))
				GenerateFaultMetadata(typeSymbol);
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
				.Union(GetSubcomponentMetadata(type))
				.Union(GetFaultMetadata(type));

			GenerateMetadataMethod(type, members);
		}

		/// <summary>
		///     Generates the metadata initialization code for the fault <paramref name="type" />.
		/// </summary>
		/// <param name="type">The component type the code should be generated for.</param>
		private void GenerateFaultMetadata(INamedTypeSymbol type)
		{
			var members = GetFieldMetadata(type)
				.Union(GetUpdateMethodMetadata(type))
				.Union(GetFaultEffectMetadata(type));

			GenerateMetadataMethod(type, members);
		}

		/// <summary>
		///     Generates the metadata initialization code for the occurrence pattern <paramref name="type" />.
		/// </summary>
		/// <param name="type">The component type the code should be generated for.</param>
		private void GenerateOccurrencePatternMetadata(INamedTypeSymbol type)
		{
			var members = GetFieldMetadata(type)
				.Union(GetUpdateMethodMetadata(type));

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
				var fieldInfo = field.GetRuntimeFieldExpression(Syntax);
				var methodName = field.Type.TypeKind == TypeKind.TypeParameter ? "WithGenericField" : "WithField";
				var withFieldMethod = Syntax.MemberAccessExpression(Syntax.IdentifierName(BuilderVariableName), methodName);
				var invocation = Syntax.InvocationExpression(withFieldMethod, fieldInfo);
				yield return (StatementSyntax)Syntax.ExpressionStatement(invocation).NormalizeWhitespace().WithTrailingNewLines(1);
			}
		}

		/// <summary>
		///     Generates the metadata initialization code for all subcomponent fields of the <paramref name="type" />.
		/// </summary>
		/// <param name="type">The type that declares the fields the metadata initialization code should be generated for.</param>
		private IEnumerable<StatementSyntax> GetSubcomponentMetadata(INamedTypeSymbol type)
		{
			var fields = type
				.GetMembers()
				.OfType<IFieldSymbol>()
				.Where(field =>
				{
					if (field.IsConst)
						return false;

					if (field.Type.TypeKind == TypeKind.TypeParameter)
						return true;

					return field.Type.ImplementsIComponent(Compilation);
				});

			foreach (var field in fields)
			{
				var fieldInfo = field.GetRuntimeFieldExpression(Syntax);
				var methodName = field.Type.TypeKind == TypeKind.TypeParameter ? "WithGenericSubcomponent" : "WithSubcomponent";
				var withSubcomponentMethod = Syntax.MemberAccessExpression(Syntax.IdentifierName(BuilderVariableName), methodName);
				var invocation = Syntax.InvocationExpression(withSubcomponentMethod, fieldInfo);
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
				var invocation = Syntax.InvocationExpression(withRequiredPortMethod, method.GetRuntimeMethodExpression(Syntax));
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
				var port = method.GetRuntimeMethodExpression(Syntax);

				var invocation = method.OverriddenMethod == null || method.OverriddenMethod.IsAbstract
					? Syntax.InvocationExpression(withProvidedPort, port)
					: Syntax.InvocationExpression(withProvidedPort, port, method.OverriddenMethod.GetRuntimeMethodExpression(Syntax));

				yield return (StatementSyntax)Syntax.ExpressionStatement(invocation).NormalizeWhitespace().WithTrailingNewLines(1);
			}
		}

		/// <summary>
		///     Generates the metadata initialization code for all fault effects of the <paramref name="type" />.
		/// </summary>
		/// <param name="type">The type that declares the fault effects the metadata initialization code should be generated for.</param>
		private IEnumerable<StatementSyntax> GetFaultEffectMetadata(INamedTypeSymbol type)
		{
			var methods = type
				.GetMembers()
				.OfType<IMethodSymbol>()
				.Where(method => method.IsFaultEffect(Compilation) && !method.IsAbstract);

			foreach (var method in methods)
			{
				var withFaultEffect = Syntax.MemberAccessExpression(Syntax.IdentifierName(BuilderVariableName), "WithFaultEffect");
				var faultEffect = method.GetRuntimeMethodExpression(Syntax);
				var affectedMethod = method.GetAffectedMethod(type.ContainingType).GetRuntimeMethodExpression(Syntax);
				var invocation = Syntax.InvocationExpression(withFaultEffect, faultEffect, affectedMethod);

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
				var overridingMethod = method.GetRuntimeMethodExpression(Syntax);
				var overriddenMethod = method.OverriddenMethod.GetRuntimeMethodExpression(Syntax);
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
	}
}