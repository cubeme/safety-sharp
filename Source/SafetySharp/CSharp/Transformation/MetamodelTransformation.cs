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
	using System.Collections.Immutable;
	using System.Linq;
	using Extensions;
	using Metamodel;
	using Metamodel.Declarations;
	using Metamodel.Statements;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Utilities;

	/// <summary>
	///     Transforms a C# compilation into a <see cref="Model" />.
	/// </summary>
	internal class MetamodelTransformation
	{
		/// <summary>
		///     The transformed component declarations.
		/// </summary>
		private readonly List<ComponentDeclaration> _components = new List<ComponentDeclaration>();

		/// <summary>
		///     The metamodel resolver that is generated during the transformation.
		/// </summary>
		private MetamodelResolver _resolver = MetamodelResolver.Empty;

		/// <summary>
		///     The symbol map that is used during the transformation.
		/// </summary>
		private SymbolMap _symbolMap = SymbolMap.Empty;

		/// <summary>
		///     Transforms the <paramref name="compilation" /> into a <see cref="Model" /> instance.
		/// </summary>
		/// <param name="compilation">The compilation that should be transformed.</param>
		public Model Transform(Compilation compilation)
		{
			Argument.NotNull(compilation, () => compilation);

			var compilationUnits = compilation.SyntaxTrees
											  .Select(syntaxTree => new CompilationUnit(syntaxTree.GetRoot(), compilation.GetSemanticModel(syntaxTree)))
											  .ToImmutableArray();

			foreach (var compilationUnit in compilationUnits)
				_symbolMap = _symbolMap.AddSymbols(compilationUnit.SemanticModel);

			foreach (var compilationUnit in compilationUnits)
				TransformCompilationUnit(compilationUnit);

			return new Model(_components.ToImmutableArray(), _resolver);
		}

		private void TransformCompilationUnit(CompilationUnit compilationUnit)
		{
			var components = compilationUnit.SyntaxRoot.DescendantNodesAndSelf()
											.OfType<ClassDeclarationSyntax>()
											.Where(classDeclaration => classDeclaration.IsComponentDeclaration(compilationUnit.SemanticModel));

			foreach (var component in components)
			{
				var componentSymbol = compilationUnit.SemanticModel.GetDeclaredSymbol(component);
				var componentReference = _symbolMap.GetComponentReference(componentSymbol);
				var componentDeclaration = TransformComponent(compilationUnit, component);

				_resolver = _resolver.With(componentReference, componentDeclaration);
				_components.Add(componentDeclaration);
			}
		}

		private ComponentDeclaration TransformComponent(CompilationUnit compilationUnit, ClassDeclarationSyntax classDeclaration)
		{
			var methods = ImmutableArray<MethodDeclaration>.Empty;
			foreach (var method in classDeclaration.Members.OfType<MethodDeclarationSyntax>())
			{
				var methodSymbol = (ITypeSymbol)compilationUnit.SemanticModel.GetDeclaredSymbol(method);
				var methodReference = _symbolMap.GetMethodReference(methodSymbol);
				var methodDeclaration = TransformMethod(compilationUnit, method);

				_resolver = _resolver.With(methodReference, methodDeclaration);
				methods = methods.Add(methodDeclaration);
			}

			var identifier = new Identifier(classDeclaration.GetFullName(compilationUnit.SemanticModel));
			return new ComponentDeclaration(identifier, null, methods);
		}

		private MethodDeclaration TransformMethod(CompilationUnit compilationUnit, MethodDeclarationSyntax methodDeclaration)
		{
			var transformation = new TransformationVisitor(compilationUnit.SemanticModel, _symbolMap);
			var body = transformation.Visit(methodDeclaration.Body) as Statement;
			Assert.NotNull(body, "Method has no body.");

			return new MethodDeclaration(new Identifier(methodDeclaration.Identifier.ValueText), body);
		}

		/// <summary>
		///     Represents a C# compilation unit that must be transformed.
		/// </summary>
		private struct CompilationUnit
		{
			/// <summary>
			///     Initializes a new instance of the <see cref="CompilationUnit" /> type.
			/// </summary>
			/// <param name="syntaxRoot">The root node of the compilation unit's syntax tree.</param>
			/// <param name="semanticModel">The semantic model for the compilation unit.</param>
			public CompilationUnit(SyntaxNode syntaxRoot, SemanticModel semanticModel)
				: this()
			{
				SyntaxRoot = syntaxRoot;
				SemanticModel = semanticModel;
			}

			/// <summary>
			///     Gets the root node of the compilation unit's syntax tree.
			/// </summary>
			public SyntaxNode SyntaxRoot { get; private set; }

			/// <summary>
			///     Gets the semantic model for the compilation unit.
			/// </summary>
			public SemanticModel SemanticModel { get; private set; }
		}
	}
}