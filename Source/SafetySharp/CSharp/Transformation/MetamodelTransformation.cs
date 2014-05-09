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
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Transforms a <see cref="ModelingCompilation" /> instance and a <see cref="ModelConfiguration" /> instance into the
	///     corresponding <see cref="MetamodelCompilation" /> and <see cref="MetamodelConfiguration" /> instances.
	/// </summary>
	internal class MetamodelTransformation
	{
		/// <summary>
		///     The modeling compilation that is being transformed.
		/// </summary>
		private readonly ModelingCompilation _compilation;

		/// <summary>
		///     The model configuration that is being transformed.
		/// </summary>
		private readonly ModelConfiguration _modelConfiguration;

		/// <summary>
		///     Initializes a new instance of the <see cref="MetamodelTransformation" /> type.
		/// </summary>
		/// <param name="compilation">The modeling compilation that should be transformed.</param>
		/// <param name="modelConfiguration">The model configuration that should be transformed.</param>
		internal MetamodelTransformation(ModelingCompilation compilation, ModelConfiguration modelConfiguration)
		{
			Argument.NotNull(compilation, () => compilation);
			Argument.NotNull(modelConfiguration, () => modelConfiguration);

			_compilation = compilation;
			_modelConfiguration = modelConfiguration;

			ComponentResolver = ComponentResolver.Empty;
			modelConfiguration.Freeze();
		}

		/// <summary>
		///     Gets the component resolver that can be used to resolve the transformed components to their corresponding metamodel
		///     component declarations.
		/// </summary>
		internal ComponentResolver ComponentResolver { get; private set; }

		/// <summary>
		///     Performs the transformation to the metamodel, returning the resulting <see cref="MetamodelCompilation" /> and
		///     <see cref="MetamodelConfiguration" /> instances on success. If any errors were encountered during the transformation,
		///     <c>false</c> is returned.
		/// </summary>
		internal bool TryTransform(out MetamodelCompilation compilation, out MetamodelConfiguration configuration)
		{
			// We're keeping a mutable array around that is used to map all component instances of the model configuration 
			// to their corresponding class declarations within the modeling compilation. The mapping is performed implicitly 
			// via the array indices of the two arrays below.
			var components = _modelConfiguration.Components;
			var classDeclarations = new ClassDeclarationSyntax[components.Length];

			for (var i = 0; i < components.Length; ++i)
				classDeclarations[i] = _compilation.GetClassDeclaration(components[i]);

			//for (var i = 0; i < _components.Length; ++i)
			//	_compilation = _compilation.Normalize1(ref _components[i].ClassDeclaration);

			//for (var i = 0; i < _components.Length; ++i)
			//	_compilation = _compilation.SubstituteGeneric(ref _components[i].ClassDeclaration, _components[i].GetType().GetGenericArguments());

			//for (var i = 0; i < _components.Length; ++i)
			//	_compilation = _compilation.Normalize2(ref _components[i].ClassDeclaration);

			// Transform the compilation 
			var compilationTransformation = new CompilationTransformation(_compilation);
			compilation = compilationTransformation.Transform();

			// Build up the required component resolver and transform the configuration
			for (var i = 0; i < components.Length; ++i)
			{
				var reference = compilationTransformation.GetComponentDeclarationReference(classDeclarations[i]);
				ComponentResolver = ComponentResolver.With(components[i], reference);
			}

			var configurationTransformation = new ConfigurationTransformation(_modelConfiguration, compilation.Resolver, ComponentResolver);
			configuration = configurationTransformation.Transform();

			return true;
		}
	}
}