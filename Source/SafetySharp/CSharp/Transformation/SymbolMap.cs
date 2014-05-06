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

namespace SafetySharp.CSharp.Transformation
{
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using Extensions;
	using Metamodel;
	using Metamodel.Declarations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Utilities;
	using Map = System.Collections.Immutable.ImmutableDictionary<Microsoft.CodeAnalysis.ISymbol, Metamodel.MetamodelReference>;

	/// <summary>
	///     Provides a mapping between C# symbols and <see cref="MetamodelReference" />s.
	/// </summary>
	internal class SymbolMap
	{
		/// <summary>
		///     The empty symbol map that does not map any symbols.
		/// </summary>
		public static readonly SymbolMap Empty = new SymbolMap { _symbolMap = Map.Empty };

		/// <summary>
		///     Maps a C# symbol to a metamodel reference.
		/// </summary>
		private Map _symbolMap;

		/// <summary>
		///     Adds the symbols declared in <paramref name="semanticModel" /> to the current <see cref="SymbolMap" /> instance.
		/// </summary>
		/// <param name="semanticModel">The semantic model containing the symbols that should be added.</param>
		public SymbolMap AddSymbols(SemanticModel semanticModel)
		{
			Argument.NotNull(semanticModel, () => semanticModel);

			var map = _symbolMap.ToBuilder();
			foreach (var reference in ResolveSymbols(semanticModel))
				map.Add((ISymbol)reference.SourceSymbol, reference);

			return new SymbolMap { _symbolMap = map.ToImmutable() };
		}

		/// <summary>
		///     Gets a typed reference to the C# <paramref name="symbol" /> representing a component.
		/// </summary>
		/// <param name="symbol">The C# symbol the reference should be returned for.</param>
		public MetamodelReference<ComponentDeclaration> GetComponentReference(ITypeSymbol symbol)
		{
			Argument.NotNull(symbol, () => symbol);
			Argument.Satisfies(symbol.TypeKind == TypeKind.Class, () => symbol, "Expected a type symbol for a class.");

			return GetReference<ComponentDeclaration>(symbol);
		}

		/// <summary>
		///     Gets a typed reference to the C# <paramref name="symbol" /> representing a method.
		/// </summary>
		/// <param name="symbol">The C# symbol the reference should be returned for.</param>
		public MetamodelReference<MethodDeclaration> GetMethodReference(IMethodSymbol symbol)
		{
			Argument.NotNull(symbol, () => symbol);
			return GetReference<MethodDeclaration>(symbol);
		}

		/// <summary>
		///     Gets a typed reference to the C# <paramref name="symbol" /> representing a field.
		/// </summary>
		/// <param name="symbol">The C# symbol the reference should be returned for.</param>
		public MetamodelReference<FieldDeclaration> GetFieldReference(IFieldSymbol symbol)
		{
			Argument.NotNull(symbol, () => symbol);
			return GetReference<FieldDeclaration>(symbol);
		}

		/// <summary>
		///     Gets a typed reference to the C# <paramref name="symbol" />.
		/// </summary>
		/// <param name="symbol">The C# symbol the reference should be returned for.</param>
		private MetamodelReference<T> GetReference<T>(ISymbol symbol)
			where T : MetamodelElement
		{
			MetamodelReference reference;
			if (!_symbolMap.TryGetValue(symbol, out reference))
				throw new InvalidOperationException("The given C# symbol is unknown.");

			Assert.OfType<MetamodelReference<T>>(reference, "Expected a metamodel reference of type '{0}' but found '{1}'.",
												 typeof(MetamodelReference<T>).FullName, reference.GetType().FullName);

			return (MetamodelReference<T>)reference;
		}

		/// <summary>
		///     Gets a value indicating whether <paramref name="symbol" /> is mapped.
		/// </summary>
		/// <param name="symbol">The symbol that should be checked.</param>
		public bool IsMapped(ISymbol symbol)
		{
			Argument.NotNull(symbol, () => symbol);
			return _symbolMap.ContainsKey(symbol);
		}

		/// <summary>
		///     Resolves all relevant symbols found within the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model for the syntax tree that should be used to resolve the C# symbols.</param>
		private static IEnumerable<MetamodelReference> ResolveSymbols(SemanticModel semanticModel)
		{
			var components = semanticModel
				.GetDeclaredComponents()
				.Select(classDeclaration =>
							new
							{
								Reference = CreateMetamodelReference<ComponentDeclaration>(semanticModel, classDeclaration),
								Declaration = classDeclaration
							})
				.ToArray();

			foreach (var component in components)
			{
				yield return component.Reference;

				var methods = component
					.Declaration
					.DescendantNodes<MethodDeclarationSyntax>()
					.Select(methodDeclaration => CreateMetamodelReference<MethodDeclaration>(semanticModel, methodDeclaration));

				foreach (var method in methods)
					yield return method;

				var fields = component
					.Declaration
					.DescendantNodes<FieldDeclarationSyntax>()
					.SelectMany(fieldDeclaration => fieldDeclaration.Declaration.Variables)
					.Select(fieldDeclaration => CreateMetamodelReference<FieldDeclaration>(semanticModel, fieldDeclaration));

				foreach (var field in fields)
					yield return field;
			}
		}

		/// <summary>
		///     Creates a new <see cref="MetamodelReference" /> instance.
		/// </summary>
		/// <typeparam name="T">The type of the metamodel element corresponding to the resolved symbol.</typeparam>
		/// <param name="semanticModel">The semantic model that should be used to resolve the C# symbol.</param>
		/// <param name="syntaxNode">The C# syntax node that should be resolved.</param>
		private static MetamodelReference CreateMetamodelReference<T>(SemanticModel semanticModel, SyntaxNode syntaxNode)
			where T : MetamodelElement
		{
			var symbol = semanticModel.GetDeclaredSymbol(syntaxNode);
			Assert.NotNull(symbol, "The semantic model could not find a symbol for '{0}' '{1}'.", syntaxNode.GetType().FullName, syntaxNode);

			return new MetamodelReference<T>(symbol);
		}
	}
}