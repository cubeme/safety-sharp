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
	///     Transforms a <see cref="ModelingCompilation" /> into a <see cref="MetamodelCompilation" /> instance.
	/// </summary>
	internal class CompilationTransformation
	{
		/// <summary>
		///     The compilation that is being transformed.
		/// </summary>
		private readonly ModelingCompilation _compilation;

		/// <summary>
		///     The metamodel resolver that is generated during the transformation.
		/// </summary>
		private MetamodelResolver _resolver = MetamodelResolver.Empty;

		/// <summary>
		///     Initializes a new instance of the <see cref="CompilationTransformation" /> type.
		/// </summary>
		/// <param name="compilation">The compilation that should be transformed.</param>
		internal CompilationTransformation(ModelingCompilation compilation)
		{
			Argument.NotNull(compilation, () => compilation);

			_compilation = compilation;
			SymbolMap = SymbolMap.Empty;
		}

		/// <summary>
		///     Gets the symbol map that is used during the transformation.
		/// </summary>
		internal SymbolMap SymbolMap { get; private set; }

		/// <summary>
		///     Gets the <see cref="MetamodelReference{ComponentDeclaration}" /> instance corresponding to the
		///     <paramref name="classDeclaration" />.
		/// </summary>
		/// <param name="classDeclaration">The class declaration the corresponding metamodel reference should be returned for.</param>
		internal MetamodelReference<ComponentDeclaration> GetComponentDeclarationReference(ClassDeclarationSyntax classDeclaration)
		{
			Argument.NotNull(classDeclaration, () => classDeclaration);

			var componentSymbol = _compilation.GetClassSymbol(classDeclaration);
			var componentReference = SymbolMap.GetComponentReference(componentSymbol);

			return componentReference;
		}

		/// <summary>
		///     Transforms the the <see cref="ModelingCompilation" /> instance passed to the constructor into a
		///     <see cref="MetamodelCompilation" /> instance.
		/// </summary>
		internal MetamodelCompilation Transform()
		{
			var semanticModels = _compilation
				.CSharpCompilation
				.SyntaxTrees
				.Select(syntaxTree => _compilation.CSharpCompilation.GetSemanticModel(syntaxTree))
				.ToImmutableArray();

			foreach (var semanticModel in semanticModels)
				SymbolMap = SymbolMap.AddSymbols(semanticModel);

			var components = semanticModels.Aggregate(
				seed: ImmutableArray<ComponentDeclaration>.Empty,
				func: (current, semanticModel) => current.AddRange(TransformComponents(semanticModel)));

			var interfaces = semanticModels.Aggregate(
				seed: ImmutableArray<InterfaceDeclaration>.Empty,
				func: (current, semanticModel) => current.AddRange(TransformInterfaces(semanticModel)));

			return new MetamodelCompilation(_resolver, components, interfaces);
		}

		/// <summary>
		///     Transforms the components within the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model containing the components that should be transformed.</param>
		private IEnumerable<ComponentDeclaration> TransformComponents(SemanticModel semanticModel)
		{
			var components = semanticModel
				.GetSyntaxRoot()
				.DescendantNodesAndSelf<ClassDeclarationSyntax>()
				.Where(classDeclaration => classDeclaration.IsComponentDeclaration(semanticModel));

			foreach (var component in components)
			{
				var componentSymbol = (ITypeSymbol)semanticModel.GetDeclaredSymbol(component);
				var componentReference = SymbolMap.GetComponentReference(componentSymbol);
				var componentDeclaration = TransformComponent(semanticModel, component);

				_resolver = _resolver.With(componentReference, componentDeclaration);
				yield return componentDeclaration;
			}
		}

		/// <summary>
		///     Transforms the component interfaces within the <paramref name="semanticModel" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model containing the component interfaces that should be transformed.</param>
		private IEnumerable<InterfaceDeclaration> TransformInterfaces(SemanticModel semanticModel)
		{
			var interfaces = semanticModel
				.GetSyntaxRoot()
				.DescendantNodesAndSelf<InterfaceDeclarationSyntax>()
				.Where(classDeclaration => classDeclaration.IsComponentInterfaceDeclaration(semanticModel));
			yield break;
			//foreach (var componentInterface in interfaces)
			//{
			//	var interfaceSymbol = (ITypeSymbol)semanticModel.GetDeclaredSymbol(componentInterface);
			//	var interfaceReference = SymbolMap.GetComponentInterfaceReference(interfaceSymbol);
			//	var interfaceDeclaration = TransformComponent(semanticModel, interfaceDeclaration);

			//	_resolver = _resolver.With(interfaceReference, interfaceDeclaration);
			//	yield return interfaceDeclaration;
			//}
		}

		/// <summary>
		///     Transforms the component declaration represented by the C# <paramref name="classDeclaration" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model the component was declared in.</param>
		/// <param name="classDeclaration">The C# class declaration that should be transformed.</param>
		private ComponentDeclaration TransformComponent(SemanticModel semanticModel, ClassDeclarationSyntax classDeclaration)
		{
			var methods = classDeclaration
				.Members
				.OfType<MethodDeclarationSyntax>()
				.Where(m => !m.IsUpdateMethod(semanticModel))
				.Aggregate(
					ImmutableArray<MethodDeclaration>.Empty,
					(current, method) => current.Add(TransformMethod(semanticModel, method)));

			var fields = classDeclaration
				.Members
				.OfType<FieldDeclarationSyntax>()
				.Aggregate(
					ImmutableArray<FieldDeclaration>.Empty,
					(current, field) => current.Add(TransformField(semanticModel, field)));

			var identifier = new Identifier(classDeclaration.GetFullName(semanticModel));
			var updateMethodDeclaration = classDeclaration
				.Members
				.OfType<MethodDeclarationSyntax>()
				.SingleOrDefault(methodDeclaration => methodDeclaration.IsUpdateMethod(semanticModel));

			var updateMethod = MethodDeclaration.UpdateMethod;
			if (updateMethodDeclaration != null)
				updateMethod = TransformMethod(semanticModel, updateMethodDeclaration);

			var subComponents = ImmutableArray<SubComponentDeclaration>.Empty;

			return new ComponentDeclaration(identifier, updateMethod, methods, fields, subComponents);
		}

		/// <summary>
		///     Transforms the method declaration represented by the C# <paramref name="methodDeclaration" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model the method was declared in.</param>
		/// <param name="methodDeclaration">The C# method declaration that should be transformed.</param>
		private MethodDeclaration TransformMethod(SemanticModel semanticModel, MethodDeclarationSyntax methodDeclaration)
		{
			var methodSymbol = (IMethodSymbol)semanticModel.GetDeclaredSymbol(methodDeclaration);
			var methodReference = SymbolMap.GetMethodReference(methodSymbol);

			var transformation = new MethodTransformation(semanticModel, SymbolMap);
			var body = (Statement)transformation.Visit(methodDeclaration.Body);

			var identifier = new Identifier(methodDeclaration.Identifier.ValueText);
			var returnType = methodSymbol.ReturnType.ToTypeSymbol(semanticModel);
			var parameters = methodSymbol.Parameters.Select(parameter =>
			{
				var name = new Identifier(parameter.Name);
				var type = parameter.Type.ToTypeSymbol(semanticModel);
				return new ParameterDeclaration(name, type);
			}).ToImmutableArray();

			var method = new MethodDeclaration(identifier, returnType, parameters, body);
			_resolver = _resolver.With(methodReference, method);

			return method;
		}

		/// <summary>
		///     Transforms the field declaration represented by the C# <paramref name="fieldDeclaration" />.
		/// </summary>
		/// <param name="semanticModel">The semantic model the method was declared in.</param>
		/// <param name="fieldDeclaration">The C# field declaration that should be transformed.</param>
		private FieldDeclaration TransformField(SemanticModel semanticModel, FieldDeclarationSyntax fieldDeclaration)
		{
			Assert.That(fieldDeclaration.Declaration.Variables.Count == 1, "Field declaration was not correctly lowered.");

			var variable = fieldDeclaration.Declaration.Variables[0];
			var fieldSymbol = (IFieldSymbol)semanticModel.GetDeclaredSymbol(variable);
			var fieldReference = SymbolMap.GetFieldReference(fieldSymbol);

			var identifier = new Identifier(variable.Identifier.ValueText);
			var field = new FieldDeclaration(identifier, fieldSymbol.Type.ToTypeSymbol(semanticModel));
			_resolver = _resolver.With(fieldReference, field);

			return field;
		}
	}
}