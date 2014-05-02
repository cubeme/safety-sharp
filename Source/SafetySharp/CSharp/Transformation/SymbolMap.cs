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

			var resolvedSymbols = ResolveSymbols(semanticModel);
			var slot = 0;

			var map = _symbolMap.ToBuilder();
			foreach (var resolvedSymbol in resolvedSymbols)
				map.Add(resolvedSymbol.Symbol, resolvedSymbol.Reference(slot++));

			return new SymbolMap { _symbolMap = map.ToImmutable() };
		}

		/// <summary>
		///     Gets a typed reference to the C# <paramref name="symbol" /> representing a component.
		/// </summary>
		/// <param name="symbol">The C# symbol the reference should be returned for.</param>
		public MetamodelReference<ComponentDeclaration> GetComponentReference(ISymbol symbol)
		{
			Argument.NotNull(symbol, () => symbol);
			Argument.OfType<ITypeSymbol>(symbol, () => symbol);

			return GetReference<ComponentDeclaration>(symbol);
		}

		/// <summary>
		///     Gets a typed reference to the C# <paramref name="symbol" /> representing a method.
		/// </summary>
		/// <param name="symbol">The C# symbol the reference should be returned for.</param>
		public MetamodelReference<MethodDeclaration> GetMethodReference(ISymbol symbol)
		{
			Argument.NotNull(symbol, () => symbol);
			Argument.OfType<IMethodSymbol>(symbol, () => symbol);

			return GetReference<MethodDeclaration>(symbol);
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
		private static IEnumerable<ResolvedSymbol> ResolveSymbols(SemanticModel semanticModel)
		{
			var root = semanticModel.SyntaxTree.GetRoot();

			var components = root.DescendantNodesAndSelf()
								 .OfType<ClassDeclarationSyntax>()
								 .Where(classDeclaration => classDeclaration.IsComponentDeclaration(semanticModel))
								 .Select(classDeclaration => ResolvedSymbol.Create<ComponentDeclaration>(semanticModel, classDeclaration))
								 .ToArray();

			foreach (var component in components)
			{
				yield return component;

				var methods = component.SyntaxNode.DescendantNodes()
									   .OfType<MethodDeclarationSyntax>()
									   .Select(methodDeclaration => ResolvedSymbol.Create<MethodDeclaration>(semanticModel, methodDeclaration));

				foreach (var method in methods)
					yield return method;
			}
		}

		/// <summary>
		///     Represents a resolved C# symbol with a generator function for the corresponding metamodel element reference.
		/// </summary>
		private struct ResolvedSymbol
		{
			/// <summary>
			///     Gets the C# syntax node corresponding to the resolved symbol.
			/// </summary>
			public SyntaxNode SyntaxNode { get; private set; }

			/// <summary>
			///     Gets the resolved C# symbol.
			/// </summary>
			public ISymbol Symbol { get; private set; }

			/// <summary>
			///     Gets the generator method for the metamodel element reference corresponding to the C# symbol.
			/// </summary>
			public Func<int, MetamodelReference> Reference { get; private set; }

			/// <summary>
			///     Creates a new <see cref="ResolvedSymbol" /> instance.
			/// </summary>
			/// <typeparam name="T">The type of the metamodel element corresponding to the resolved symbol.</typeparam>
			/// <param name="semanticModel">The semantic model that should be used to resolve the C# symbol.</param>
			/// <param name="syntaxNode">The C# syntax node that should be resolved.</param>
			public static ResolvedSymbol Create<T>(SemanticModel semanticModel, SyntaxNode syntaxNode)
				where T : MetamodelElement
			{
				return new ResolvedSymbol
				{
					SyntaxNode = syntaxNode,
					Symbol = semanticModel.GetDeclaredSymbol(syntaxNode),
					Reference = slot => new MetamodelReference<T>(slot)
				};
			}
		}
	}
}