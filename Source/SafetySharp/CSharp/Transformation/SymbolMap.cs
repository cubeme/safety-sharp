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
	using Metamodel;
	using Metamodel.Declarations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Utilities;

	internal class SymbolMap
	{
		/// <summary>
		///     Maps a C# symbol to a slot in the metamodel element map.
		/// </summary>
		private readonly Dictionary<ISymbol, int> _symbolMap = new Dictionary<ISymbol, int>(1024);

		/// <summary>
		///     The next free symbol slot that is used when a new C# symbol is added.
		/// </summary>
		private int _nextSymbolSlot;

		/// <summary>
		///     Initializes a new instance of the <see cref="SymbolMap" /> type.
		/// </summary>
		/// <param name="compilation">The compilation the symbol map should be generated for.</param>
		public SymbolMap(Compilation compilation)
		{
			foreach (var syntaxTree in compilation.SyntaxTrees)
			{
				var semanticModel = compilation.GetSemanticModel(syntaxTree);

				Add<BaseTypeDeclarationSyntax>(semanticModel, syntaxTree);
				Add<MethodDeclarationSyntax>(semanticModel, syntaxTree);
			}
		}

		/// <summary>
		///     Gets a typed reference to the C# <paramref name="symbol" /> representing a component.
		/// </summary>
		/// <param name="symbol">The C# symbol the reference should be returned for.</param>
		public Reference<ComponentDeclaration> GetComponentReference(ISymbol symbol)
		{
			Assert.ArgumentNotNull(symbol, () => symbol);
			Assert.ArgumentOfType<ITypeSymbol>(symbol, () => symbol);

			return GetReference<ComponentDeclaration>(symbol);
		}

		/// <summary>
		///     Gets a typed reference to the C# <paramref name="symbol" /> representing a method.
		/// </summary>
		/// <param name="symbol">The C# symbol the reference should be returned for.</param>
		public Reference<MethodDeclaration> GetMethodReference(ISymbol symbol)
		{
			Assert.ArgumentNotNull(symbol, () => symbol);
			Assert.ArgumentOfType<IMethodSymbol>(symbol, () => symbol);

			return GetReference<MethodDeclaration>(symbol);
		}

		/// <summary>
		///     Gets a typed reference to the C# <paramref name="symbol" />.
		/// </summary>
		/// <param name="symbol">The C# symbol the reference should be returned for.</param>
		private Reference<T> GetReference<T>(ISymbol symbol)
			where T : MetamodelElement
		{
			int slot;
			if (!_symbolMap.TryGetValue(symbol, out slot))
				Assert.NotReached("The given C# symbol is unknown.");

			return new Reference<T>(slot);
		}

		/// <summary>
		///     Gets a value indicating whether <paramref name="symbol" /> is contained in the <see cref="SymbolMap" />.
		/// </summary>
		/// <param name="symbol">The symbol that should be checked.</param>
		public bool Contains(ISymbol symbol)
		{
			Assert.ArgumentNotNull(symbol, () => symbol);
			return _symbolMap.ContainsKey(symbol);
		}

		private void Add<T>(SemanticModel semanticModel, SyntaxTree syntaxTree)
			where T : SyntaxNode
		{
			var symbols = syntaxTree.GetRoot()
									.DescendantNodesAndSelf()
									.OfType<T>()
									.Select(declaration => semanticModel.GetDeclaredSymbol(declaration));

			foreach (var symbol in symbols)
				_symbolMap.Add(symbol, _nextSymbolSlot++);
		}
	}
}