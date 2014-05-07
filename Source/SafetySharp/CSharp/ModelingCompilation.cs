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

namespace SafetySharp.CSharp
{
	using System;
	using System.Collections.Immutable;
	using System.Linq;
	using Extensions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Represents a compilation of a Safety Sharp modeling assembly.
	/// </summary>
	internal class ModelingCompilation
	{
		/// <summary>
		///     Initializes a new instance of the <see cref="ModelingCompilation" /> type.
		/// </summary>
		/// <param name="compilation">The C# compilation that represents the modeling compilation.</param>
		internal ModelingCompilation(Compilation compilation)
		{
			Argument.NotNull(compilation, () => compilation);
			CSharpCompilation = compilation;
		}

		/// <summary>
		///     Gets the C# compilation that represents the modeling compilation.
		/// </summary>
		internal Compilation CSharpCompilation { get; private set; }

		internal ModelingCompilation Normalize1(ref ClassDeclarationSyntax classDeclaration)
		{
			return null;
		}

		internal ModelingCompilation SubstituteGeneric(ref ClassDeclarationSyntax classDeclaration, Type[] types)
		{
			return null;
		}

		internal ModelingCompilation Normalize2(ref ClassDeclarationSyntax classDeclaration)
		{
			return null;
		}

		/// <summary>
		///     Gets the <see cref="ClassDeclarationSyntax" /> corresponding to the <paramref name="component" />.
		/// </summary>
		/// <param name="component">The component the class declaration should be returned for.</param>
		internal ClassDeclarationSyntax GetClassDeclaration(Component component)
		{
			Argument.NotNull(component, () => component);

			var componentType = component.GetType();
			var componentClass = (from syntaxTree in CSharpCompilation.SyntaxTrees
								  let semanticModel = CSharpCompilation.GetSemanticModel(syntaxTree)
								  from classDeclaration in syntaxTree.DescendantNodesAndSelf<ClassDeclarationSyntax>()
								  where classDeclaration.GetFullName(semanticModel) == componentType.FullName
								  select classDeclaration).ToImmutableArray();

			const string messageNone = "Unable to find a class declaration corresponding to type '{0}' in the modeling assembly metadata.";
			const string messageMany = "Found more than one class declarations corresponding to type '{0}' in the modeling assembly metadata.";

			if (componentClass.Length == 0)
				throw new InvalidOperationException(String.Format(messageNone, componentType.FullName));

			if (componentClass.Length > 1)
				throw new InvalidOperationException(String.Format(messageMany, componentType.FullName));

			return componentClass[0];
		}
	}
}