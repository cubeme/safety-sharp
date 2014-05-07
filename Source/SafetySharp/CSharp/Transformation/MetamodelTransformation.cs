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

	internal class MetamodelTransformation
	{
		private readonly ModelConfiguration _modelConfiguration;
		private ModelingCompilation _compilation;
		private ComponentMapping[] _components;

		public MetamodelTransformation(ModelingCompilation compilation, ModelConfiguration modelConfiguration)
		{
			_compilation = compilation;
			_modelConfiguration = modelConfiguration;
		}

		internal Model Transform()
		{
			for (var i = 0; i < _components.Length; ++i)
				_compilation = _compilation.Normalize1(ref _components[i].ClassDeclaration);

			for (var i = 0; i < _components.Length; ++i)
				_compilation = _compilation.SubstituteGeneric(ref _components[i].ClassDeclaration, _components[i].GetType().GetGenericArguments());

			for (var i = 0; i < _components.Length; ++i)
				_compilation = _compilation.Normalize2(ref _components[i].ClassDeclaration);

			var compilationTransformation = new CompilationTransformation();
			var model = compilationTransformation.Transform(_compilation.CSharpCompilation);

			var partitionTransformation = new PartitionTransformation(model);
			return partitionTransformation.Transform(_modelConfiguration.PartitionRoots);
		}

		private void CollectComponents(Component component)
		{
			_components[0].ClassDeclaration = _compilation.GetClassDeclaration(component);
			// recursive add components....
		}

		private struct ComponentMapping
		{
			public ClassDeclarationSyntax ClassDeclaration;
			public Component Component;
		}
	}
}