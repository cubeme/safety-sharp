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
	using Metamodel;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Utilities;

	/// <summary>
	///     Transforms a lowered C# syntax tree of a method or property body into a corresponding metamodel element tree.
	/// </summary>
	internal partial class MethodTransformation : CSharpSyntaxVisitor<MetamodelElement>
	{
		/// <summary>
		///     The semantic model that can be used to retrieve semantic information about the C# program.
		/// </summary>
		private readonly SemanticModel _semanticModel;

		/// <summary>
		///     The symbol map that can be used to look up metamodel element references for C# symbols.
		/// </summary>
		private readonly SymbolMap _symbolMap;

		/// <summary>
		///     Initializes a new instance of the <see cref="MethodTransformation" /> type.
		/// </summary>
		/// <param name="semanticModel">The semantic model that should be used to retrieve semantic information about the C# program.</param>
		/// <param name="symbolMap">The symbol map that should be used to look up metamodel element references for C# symbols.</param>
		internal MethodTransformation(SemanticModel semanticModel, SymbolMap symbolMap)
		{
			Argument.NotNull(semanticModel, () => semanticModel);
			Argument.NotNull(symbolMap, () => symbolMap);

			_semanticModel = semanticModel;
			_symbolMap = symbolMap;
		}

		/// <summary>
		///     Raises an exception for all unsupported C# features found in the lowered C# syntax tree.
		/// </summary>
		/// <param name="node">The syntax node of the unsupported C# feature.</param>
		public override MetamodelElement DefaultVisit(SyntaxNode node)
		{
			Assert.NotReached("Encountered an unexpected C# syntax node: '{0}'.", node.CSharpKind());
			return null;
		}
	}
}