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

namespace SafetySharp.CSharp.Extensions
{
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with <see cref="SemanticModel" /> instances.
	/// </summary>
	internal static class SemanticModelExtensions
	{
		/// <summary>
		///     Gets the components declared within the context of the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model containing the declared components.</param>
		internal static IEnumerable<ClassDeclarationSyntax> GetDeclaredComponents(this SemanticModel semanticModel)
		{
			Argument.NotNull(semanticModel, () => semanticModel);

			return semanticModel
				.SyntaxTree
				.DescendantNodesAndSelf<ClassDeclarationSyntax>()
				.Where(classDeclaration => classDeclaration.IsComponentDeclaration(semanticModel));
		}

		/// <summary>
		///     Gets the component interfaces declared within the context of the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model containing the declared component interfaces.</param>
		internal static IEnumerable<InterfaceDeclarationSyntax> GetDeclaredComponentInterfaces(this SemanticModel semanticModel)
		{
			Argument.NotNull(semanticModel, () => semanticModel);

			return semanticModel
				.SyntaxTree
				.DescendantNodesAndSelf<InterfaceDeclarationSyntax>()
				.Where(interfaceDeclaration => interfaceDeclaration.IsComponentInterfaceDeclaration(semanticModel));
		}

		/// <summary>
		///     Gets the root node of the <paramref name="semanticModel" />'s <see cref="SyntaxTree" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model the syntax root should be returned for.</param>
		internal static SyntaxNode GetSyntaxRoot(this SemanticModel semanticModel)
		{
			Argument.NotNull(semanticModel, () => semanticModel);
			return semanticModel.SyntaxTree.GetRoot();
		}

		/// <summary>
		///     Gets the <see cref="ITypeSymbol" /> representing the type <typeparamref name="T"/> within the context of
		///     the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model the type symbol should be returned for.</param>
		internal static ITypeSymbol GetTypeSymbol<T>(this SemanticModel semanticModel)
		{
			Argument.NotNull(semanticModel, () => semanticModel);
			return semanticModel.Compilation.GetTypeByMetadataName(typeof(T).FullName);
		}

		/// <summary>
		///     Gets the <see cref="IMethodSymbol " /> representing the <see cref="Component.Choose{T}()" />
		///     method within the context of the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model that should be used to retrieve the symbol.</param>
		internal static IMethodSymbol GetChooseEnumerationLiteralMethodSymbol(this SemanticModel semanticModel)
		{
			Argument.NotNull(semanticModel, () => semanticModel);
			return GetChooseMethodSymbol(semanticModel, 0);
		}

		/// <summary>
		///     Gets the <see cref="IMethodSymbol " /> representing the <see cref="Component.Choose{T}(T, T, T[])" /> method within the
		///     context of the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model that should be used to retrieve the symbol.</param>
		/// <param name="normalizedMethod">If <c>true</c>, returns the symbol for the normalized method.</param>
		internal static IMethodSymbol GetChooseFromValuesMethodSymbol(this SemanticModel semanticModel, bool normalizedMethod)
		{
			Argument.NotNull(semanticModel, () => semanticModel);
			return GetChooseMethodSymbol(semanticModel, normalizedMethod ? 4 : 3);
		}

		/// <summary>
		///     Gets the <see cref="IMethodSymbol " /> representing the <see cref="Component.ChooseFromRange(int, int)" /> method within
		///     the context of the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model that should be used to retrieve the symbol.</param>
		/// <param name="normalizedMethod">If <c>true</c>, returns the symbol for the normalized method.</param>
		internal static IMethodSymbol GetChooseFromIntegerRangeMethodSymbol(this SemanticModel semanticModel, bool normalizedMethod)
		{
			Argument.NotNull(semanticModel, () => semanticModel);
			return GetChooseRangeMethodSymbol(semanticModel, SpecialType.System_Int32, normalizedMethod ? 3 : 2);
		}

		/// <summary>
		///     Gets the <see cref="IMethodSymbol " /> representing the
		///     <see cref="Component.ChooseFromRange(out decimal, decimal, decimal)" /> method within the context
		///     of the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model that should be used to retrieve the symbol.</param>
		/// <param name="normalizedMethod">If <c>true</c>, returns the symbol for the normalized method.</param>
		internal static IMethodSymbol GetChooseFromDecimalRangeMethodSymbol(this SemanticModel semanticModel, bool normalizedMethod)
		{
			Argument.NotNull(semanticModel, () => semanticModel);
			return GetChooseRangeMethodSymbol(semanticModel, SpecialType.System_Decimal, normalizedMethod ? 3 : 2);
		}

		/// <summary>
		///     Gets the <see cref="ITypeSymbol " /> representing the <see cref="Component" /> class within the
		///     context of the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model that should be used to retrieve the symbol.</param>
		internal static ITypeSymbol GetComponentClassSymbol(this SemanticModel semanticModel)
		{
			Argument.NotNull(semanticModel, () => semanticModel);
			return semanticModel.Compilation.GetTypeByMetadataName(typeof(Component).FullName);
		}

		/// <summary>
		///     Gets the <see cref="ITypeSymbol " /> representing the <see cref="IComponent" /> interface within the
		///     context of the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model that should be used to retrieve the symbol.</param>
		internal static ITypeSymbol GetComponentInterfaceSymbol(this SemanticModel semanticModel)
		{
			Argument.NotNull(semanticModel, () => semanticModel);
			return semanticModel.Compilation.GetTypeByMetadataName(typeof(IComponent).FullName);
		}

		/// <summary>
		///     Gets the <see cref="IMethodSymbol " /> representing the <see cref="Component.Update()" /> method
		///     within the context of the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model that should be used to retrieve the symbol.</param>
		internal static IMethodSymbol GetUpdateMethodSymbol(this SemanticModel semanticModel)
		{
			Argument.NotNull(semanticModel, () => semanticModel);
			return semanticModel.GetComponentClassSymbol().GetMembers("Update").OfType<IMethodSymbol>().Single();
		}

		/// <summary>
		///     Gets the <see cref="IMethodSymbol" /> corresponding to the one of the 'Component.Choose' methods.
		/// </summary>
		/// <param name="semanticModel">The semantic model containing the declared components.</param>
		/// <param name="parameterCount">The number of parameters of the method.</param>
		private static IMethodSymbol GetChooseMethodSymbol(SemanticModel semanticModel, int parameterCount)
		{
			return semanticModel
				.GetComponentClassSymbol()
				.GetMembers("Choose")
				.OfType<IMethodSymbol>()
				.Single(method => method.Parameters.Length == parameterCount);
		}

		/// <summary>
		///     Gets the <see cref="IMethodSymbol" /> corresponding to the one of the 'Component.ChooseFromRange' methods.
		/// </summary>
		/// <param name="semanticModel">The semantic model containing the declared components.</param>
		/// <param name="type">The type of the method's parameters.</param>
		/// <param name="parameterCount">The number of parameters of the method.</param>
		private static IMethodSymbol GetChooseRangeMethodSymbol(SemanticModel semanticModel, SpecialType type, int parameterCount)
		{
			return semanticModel
				.GetComponentClassSymbol()
				.GetMembers("ChooseFromRange")
				.OfType<IMethodSymbol>()
				.Single(method => method.Parameters[0].Type.SpecialType == type && method.Parameters.Length == parameterCount);
		}
	}
}