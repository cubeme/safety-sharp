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

namespace SafetySharp.Compiler.Roslyn.Symbols
{
	using System;
	using System.Linq;
	using CompilerServices;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Editing;
	using Modeling;
	using Modeling.Faults;
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with <see cref="IMethodSymbol" /> instances.
	/// </summary>
	public static class MethodSymbolExtensions
	{
		/// <summary>
		///     Checks whether <paramref name="methodSymbol" /> overrides <paramref name="overriddenMethod" />.
		/// </summary>
		/// <param name="methodSymbol">The symbol of the methodSymbol that should be checked.</param>
		/// <param name="overriddenMethod">The symbol of the methodSymbol that should be overridden.</param>
		[Pure]
		public static bool Overrides([NotNull] this IMethodSymbol methodSymbol, [NotNull] IMethodSymbol overriddenMethod)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(overriddenMethod, () => overriddenMethod);

			if (methodSymbol.Equals(overriddenMethod))
				return true;

			if (!methodSymbol.IsOverride)
				return false;

			if (methodSymbol.OverriddenMethod.Equals(overriddenMethod))
				return true;

			return methodSymbol.OverriddenMethod.Overrides(overriddenMethod);
		}

		/// <summary>
		///     Checks whether <paramref name="methodSymbol" /> replaces <paramref name="replacedMethod" />.
		/// </summary>
		/// <param name="methodSymbol">The symbol of the methodSymbol that should be checked.</param>
		/// <param name="replacedMethod">The symbol of the methodSymbol that should be replaced.</param>
		[Pure]
		public static bool Replaces([NotNull] this IMethodSymbol methodSymbol, [NotNull] IMethodSymbol replacedMethod)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(replacedMethod, () => replacedMethod);

			if (methodSymbol.Equals(replacedMethod))
				return true;

			if (methodSymbol.Name != replacedMethod.Name)
				return false;

			if (!methodSymbol.ContainingType.IsDerivedFrom(replacedMethod.ContainingType))
				return false;

			if (methodSymbol.Overrides(replacedMethod))
				return false;

			return methodSymbol.IsSignatureCompatibleTo(replacedMethod);
		}

		/// <summary>
		///     Checks whether <paramref name="methodSymbol" /> overrides <see cref="Component.Update()" />,
		///     <see cref="Fault.UpdateFaultState" />, or <see cref="OccurrencePattern.UpdateOccurrenceState" /> within the
		///     context of the <paramref name="compilation" />.
		/// </summary>
		/// <param name="methodSymbol">The methodSymbol symbol that should be checked.</param>
		/// <param name="compilation">The compilation that should be used to resolve symbol information.</param>
		[Pure]
		public static bool IsUpdateMethod([NotNull] this IMethodSymbol methodSymbol, [NotNull] Compilation compilation)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(compilation, () => compilation);

			if (methodSymbol.HasAttribute<SuppressTransformationAttribute>(compilation))
				return false;

			return methodSymbol.Overrides(compilation.GetComponentUpdateMethodSymbol()) ||
				   methodSymbol.Overrides(compilation.GetFaultUpdateMethodSymbol()) ||
				   methodSymbol.Overrides(compilation.GetOccurrencePatternUpdateMethodSymbol());
		}

		/// <summary>
		///     Checks whether <paramref name="methodSymbol" /> overrides <see cref="Component.Update()" />,
		///     <see cref="Fault.UpdateFaultState" />, or <see cref="OccurrencePattern.UpdateOccurrenceState" /> within the
		///     context of the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="methodSymbol">The methodSymbol symbol that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve symbol information.</param>
		[Pure]
		public static bool IsUpdateMethod([NotNull] this IMethodSymbol methodSymbol, [NotNull] SemanticModel semanticModel)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(semanticModel, () => semanticModel);

			return methodSymbol.IsUpdateMethod(semanticModel.Compilation);
		}

		/// <summary>
		///     Checks whether <paramref name="methodSymbol" /> represents a required port of a S# component or interface.
		/// </summary>
		/// <param name="methodSymbol">The methodSymbol symbol that should be checked.</param>
		/// <param name="compilation">The compilation that should be used to resolve symbol information.</param>
		[Pure]
		public static bool IsRequiredPort([NotNull] this IMethodSymbol methodSymbol, [NotNull] Compilation compilation)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(compilation, () => compilation);

			if (methodSymbol.IsStatic)
				return false;

			if (methodSymbol.MethodKind != MethodKind.Ordinary && methodSymbol.MethodKind != MethodKind.ExplicitInterfaceImplementation)
				return false;

			if (!methodSymbol.ContainingType.ImplementsIComponent(compilation))
				return false;

			if (methodSymbol.HasAttribute<SuppressTransformationAttribute>(compilation))
				return false;

			switch (methodSymbol.ContainingType.TypeKind)
			{
				case TypeKind.Class:
					return methodSymbol.IsExtern || methodSymbol.HasAttribute<RequiredAttribute>(compilation);
				case TypeKind.Interface:
					return methodSymbol.HasAttribute<RequiredAttribute>(compilation);
				default:
					return false;
			}
		}

		/// <summary>
		///     Checks whether <paramref name="methodSymbol" /> represents a required port of a S# component or interface.
		/// </summary>
		/// <param name="methodSymbol">The methodSymbol symbol that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve symbol information.</param>
		[Pure]
		public static bool IsRequiredPort([NotNull] this IMethodSymbol methodSymbol, [NotNull] SemanticModel semanticModel)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(semanticModel, () => semanticModel);

			return methodSymbol.IsRequiredPort(semanticModel.Compilation);
		}

		/// <summary>
		///     Checks whether <paramref name="methodSymbol" /> represents a provided port of a S# component or interface.
		/// </summary>
		/// <param name="methodSymbol">The methodSymbol symbol that should be checked.</param>
		/// <param name="compilation">The compilation that should be used to resolve symbol information.</param>
		[Pure]
		public static bool IsProvidedPort([NotNull] this IMethodSymbol methodSymbol, [NotNull] Compilation compilation)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(compilation, () => compilation);

			if (methodSymbol.IsStatic)
				return false;

			if (methodSymbol.MethodKind != MethodKind.Ordinary && methodSymbol.MethodKind != MethodKind.ExplicitInterfaceImplementation)
				return false;

			if (!methodSymbol.ContainingType.ImplementsIComponent(compilation))
				return false;

			if (methodSymbol.HasAttribute<SuppressTransformationAttribute>(compilation))
				return false;

			switch (methodSymbol.ContainingType.TypeKind)
			{
				case TypeKind.Class:
					return !methodSymbol.IsExtern &&
						   !methodSymbol.HasAttribute<RequiredAttribute>(compilation) &&
						   !methodSymbol.IsUpdateMethod(compilation);
				case TypeKind.Interface:
					return methodSymbol.HasAttribute<ProvidedAttribute>(compilation);
				default:
					return false;
			}
		}

		/// <summary>
		///     Checks whether <paramref name="methodSymbol" /> represents a provided port of a S# component or interface.
		/// </summary>
		/// <param name="methodSymbol">The methodSymbol symbol that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve symbol information.</param>
		[Pure]
		public static bool IsProvidedPort([NotNull] this IMethodSymbol methodSymbol, [NotNull] SemanticModel semanticModel)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(semanticModel, () => semanticModel);

			return methodSymbol.IsProvidedPort(semanticModel.Compilation);
		}

		/// <summary>
		///     Checks whether <paramref name="methodSymbol" /> represents a fault effect of a S# fault.
		/// </summary>
		/// <param name="methodSymbol">The methodSymbol symbol that should be checked.</param>
		/// <param name="compilation">The compilation that should be used to resolve symbol information.</param>
		[Pure]
		public static bool IsFaultEffect([NotNull] this IMethodSymbol methodSymbol, [NotNull] Compilation compilation)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(compilation, () => compilation);

			if (methodSymbol.IsStatic)
				return false;

			if (methodSymbol.MethodKind != MethodKind.Ordinary && methodSymbol.MethodKind != MethodKind.ExplicitInterfaceImplementation)
				return false;

			if (!methodSymbol.ContainingType.IsDerivedFromFault(compilation))
				return false;

			if (methodSymbol.HasAttribute<SuppressTransformationAttribute>(compilation))
				return false;

			if (methodSymbol.IsUpdateMethod(compilation))
				return false;

			return true;
		}

		/// <summary>
		///     Checks whether <paramref name="methodSymbol" /> represents a fault effect of a S# fault.
		/// </summary>
		/// <param name="methodSymbol">The methodSymbol symbol that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve symbol information.</param>
		[Pure]
		public static bool IsFaultEffect([NotNull] this IMethodSymbol methodSymbol, [NotNull] SemanticModel semanticModel)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(semanticModel, () => semanticModel);

			return methodSymbol.IsFaultEffect(semanticModel.Compilation);
		}

		/// <summary>
		///     Checks whether <paramref name="methodSymbol" /> represents a built-in operator of the <see cref="int" />,
		///     <see cref="bool" />, or <see cref="decimal" /> types.
		/// </summary>
		/// <param name="methodSymbol">The methodSymbol symbol that should be checked.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve symbol information.</param>
		[Pure]
		public static bool IsBuiltInOperator([NotNull] this IMethodSymbol methodSymbol, [NotNull] SemanticModel semanticModel)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(semanticModel, () => semanticModel);

			return methodSymbol.ContainingType.Equals(semanticModel.GetTypeSymbol<int>()) ||
				   methodSymbol.ContainingType.Equals(semanticModel.GetTypeSymbol<bool>()) ||
				   methodSymbol.ContainingType.Equals(semanticModel.GetTypeSymbol<decimal>());
		}

		/// <summary>
		///     Gets the <see cref="IMethodSymbol" /> representing the method declared by <paramref name="affectedType" /> that is
		///     affected by <paramref name="faultEffect" />.
		/// </summary>
		/// <param name="faultEffect">The fault effect the affected method should be returned for.</param>
		/// <param name="affectedType">The type that is affected by the fault.</param>
		[Pure]
		public static IMethodSymbol GetAffectedMethod([NotNull] this IMethodSymbol faultEffect, INamedTypeSymbol affectedType)
		{
			Requires.NotNull(faultEffect, () => faultEffect);

			var candidateMethods = affectedType
				.GetMembers()
				.OfType<IMethodSymbol>()
				.Where(candidate => candidate.MethodKind == MethodKind.Ordinary || candidate.MethodKind == MethodKind.ExplicitInterfaceImplementation)
				.Where(candidate => candidate.MethodKind == MethodKind.ExplicitInterfaceImplementation
						? candidate.ExplicitInterfaceImplementations[0].Name == faultEffect.Name
						: candidate.Name == faultEffect.Name)
				.Where(candidate => candidate.IsSignatureCompatibleTo(faultEffect))
				.ToArray();

			Requires.That(candidateMethods.Length == 1, "Failed to uniquely determine the affected method of fault effect '{0}'.",
				faultEffect.ToDisplayString());

			return candidateMethods[0];
		}

		/// <summary>
		///     Returns a <see cref="DelegateDeclarationSyntax" /> for a delegate that can be used to invoke
		///     <paramref name="methodSymbol" />.
		/// </summary>
		/// <param name="methodSymbol">The methodSymbol the delegate should be synthesized for.</param>
		/// <param name="name">An name of the synthesized delegate.</param>
		[Pure]
		public static DelegateDeclarationSyntax GetSynthesizedDelegateDeclaration([NotNull] this IMethodSymbol methodSymbol, [NotNull] string name)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNullOrWhitespace(name, () => name);

			var returnType = SyntaxFactory.ParseTypeName(methodSymbol.ReturnType.ToDisplayString());
			var parameters = methodSymbol.Parameters.Select(parameter =>
			{
				var identifier = SyntaxFactory.Identifier(parameter.Name);
				var type = SyntaxFactory.ParseTypeName(parameter.Type.ToDisplayString());

				SyntaxKind? keyword = null;
				if (parameter.IsParams)
					keyword = SyntaxKind.ParamsKeyword;

				switch (parameter.RefKind)
				{
					case RefKind.None:
						break;
					case RefKind.Ref:
						keyword = SyntaxKind.RefKeyword;
						break;
					case RefKind.Out:
						keyword = SyntaxKind.OutKeyword;
						break;
					default:
						throw new InvalidOperationException("Unsupported ref kind.");
				}

				var declaration = SyntaxFactory.Parameter(identifier).WithType(type);
				if (keyword != null)
					declaration = declaration.WithModifiers(SyntaxFactory.TokenList(SyntaxFactory.Token(keyword.Value)));

				return declaration;
			});

			return SyntaxFactory
				.DelegateDeclaration(returnType, name)
				.WithModifiers(SyntaxTokenList.Create(SyntaxFactory.Token(SyntaxKind.PrivateKeyword)))
				.WithParameterList(SyntaxFactory.ParameterList(SyntaxFactory.SeparatedList(parameters)))
				.NormalizeWhitespace();
		}

		/// <summary>
		///     Checks whether the two <see cref="IMethodSymbol" />s are signature-compatible.
		/// </summary>
		/// <param name="methodSymbol1">The first methodSymbol symbol that should be checked.</param>
		/// <param name="methodSymbol2">The second methodSymbol symbol that should be checked.</param>
		public static bool IsSignatureCompatibleTo([NotNull] this IMethodSymbol methodSymbol1, [NotNull] IMethodSymbol methodSymbol2)
		{
			Requires.NotNull(methodSymbol1, () => methodSymbol1);
			Requires.NotNull(methodSymbol2, () => methodSymbol2);

			if (methodSymbol1.TypeParameters.Length != 0 || methodSymbol2.TypeParameters.Length != 0)
				return false;

			return methodSymbol1.ReturnType.Equals(methodSymbol2.ReturnType)
				   && methodSymbol1.Parameters.Length == methodSymbol2.Parameters.Length
				   && methodSymbol1.Parameters
								   .Zip(methodSymbol2.Parameters, (p1, p2) => p1.Type.Equals(p2.Type) && p1.RefKind == p2.RefKind)
								   .All(b => b);
		}

		/// <summary>
		///     Gets the expression that selects the <paramref name="methodSymbol" /> at runtime using reflection.
		/// </summary>
		/// <param name="methodSymbol">The methodSymbol the code should be created for.</param>
		/// <param name="syntaxGenerator">The syntax generator that should be used.</param>
		/// <param name="methodName">
		///     The name of the method that should be used; if <c>null</c>, <see cref="methodSymbol" />'s name is
		///     used instead.
		/// </param>
		/// <param name="declaringType">
		///     The declaring type that should be used; if <c>null</c>, <see cref="methodSymbol" />'s declaring
		///     type is used instead.
		/// </param>
		public static ExpressionSyntax GetRuntimeMethodExpression([NotNull] this IMethodSymbol methodSymbol,
																  [NotNull] SyntaxGenerator syntaxGenerator,
																  string methodName = null,
																  string declaringType = null)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			Requires.NotNull(syntaxGenerator, () => syntaxGenerator);

			var declaringTypeArg = declaringType == null
				? SyntaxFactory.TypeOfExpression((TypeSyntax)syntaxGenerator.TypeExpression(methodSymbol.ContainingType))
				: SyntaxFactory.TypeOfExpression(SyntaxFactory.ParseTypeName(declaringType));
			var parameters = GetParameterTypeArray(methodSymbol, syntaxGenerator);
			var returnType = SyntaxFactory.TypeOfExpression((TypeSyntax)syntaxGenerator.TypeExpression(methodSymbol.ReturnType));
			var nameArg = syntaxGenerator.LiteralExpression(methodName ?? methodSymbol.Name);
			var reflectionHelpersType = SyntaxFactory.ParseTypeName(typeof(ReflectionHelpers).FullName);
			var getMethodMethod = syntaxGenerator.MemberAccessExpression(reflectionHelpersType, "GetMethod");
			return (ExpressionSyntax)syntaxGenerator.InvocationExpression(getMethodMethod, declaringTypeArg, nameArg, parameters, returnType);
		}

		/// <summary>
		///     Gets the parameter type array that can be used to retrieve the <paramref name="methodSymbol" /> via reflection.
		/// </summary>
		/// <param name="methodSymbol">The method the parameter type array should be returned for.</param>
		/// <param name="syntaxGenerator">The syntax generator that should be used.</param>
		private static ExpressionSyntax GetParameterTypeArray([NotNull] this IMethodSymbol methodSymbol,
															  [NotNull] SyntaxGenerator syntaxGenerator)
		{
			var typeExpressions = methodSymbol.Parameters.Select(p =>
			{
				var typeofExpression = SyntaxFactory.TypeOfExpression((TypeSyntax)syntaxGenerator.TypeExpression(p.Type));
				if (p.RefKind == RefKind.None)
					return typeofExpression;

				var makeRefType = syntaxGenerator.MemberAccessExpression(typeofExpression, "MakeByRefType");
				return (ExpressionSyntax)syntaxGenerator.InvocationExpression(makeRefType);
			});

			var arguments = SyntaxFactory.SeparatedList(typeExpressions);
			var initialize = SyntaxFactory.InitializerExpression(SyntaxKind.ArrayInitializerExpression, arguments);
			var arrayType = syntaxGenerator.ArrayTypeExpression(SyntaxFactory.ParseTypeName(typeof(Type).FullName));
			return SyntaxFactory.ArrayCreationExpression((ArrayTypeSyntax)arrayType, initialize);
		}
	}
}