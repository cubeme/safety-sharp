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

namespace Tests.CSharp.Transformation
{
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.CSharp;
	using SafetySharp.CSharp.Transformation;
	using SafetySharp.Metamodel;
	using SafetySharp.Modeling;

	[TestFixture]
	internal class MetamodelTransformationTests
	{
		private class TestConfiguration : ModelConfiguration
		{
			public TestConfiguration(params Component[] components)
			{
				AddPartitions(components);
			}
		}

		private MetamodelCompilation _compilation;
		private MetamodelConfiguration _configuration;
		private ComponentResolver _componentResolver;
		private Dictionary<string, Component> _components;

		private void Transform(string csharpCode, params string[] componentNames)
		{
			csharpCode = "using SafetySharp.Modeling; " + csharpCode;
			var compilation = new TestCompilation(csharpCode);
			var assembly = compilation.Compile();

			var compilationTransformation = new CompilationTransformation(new ModelingCompilation(compilation.Compilation));
			_compilation = compilationTransformation.Transform();

			_components =new Dictionary<string, Component>();
			_componentResolver = ComponentResolver.Empty;

			foreach (var componentName in componentNames)
			{
				var component = (Component)Activator.CreateInstance(assembly.GetType(componentName));
				_components.Add(componentName, component);

				var reference = compilationTransformation.GetComponentDeclarationReference(compilation.FindClassDeclaration(componentName));
				_componentResolver = _componentResolver.With(component, reference);
			}

			var configuration = new TestConfiguration(_components.Values.ToArray());
			var configurationTransformation = new ConfigurationTransformation(configuration, _compilation.Resolver, _componentResolver);
			_configuration = configurationTransformation.Transform();
		}

		[Test]
		public void Test()
		{
			var csharpCode = @"
class X : Component
{
	private int _field;		

	public X()
	{
		SetInitialValues(() => _field, 1, 2, 3, 4, 5, 6);
	}
}";
			Transform(csharpCode, "X");
			_configuration.Partitions.Should().HaveCount(1);

			var componentConfiguration = _configuration.Partitions[0].Component;
			componentConfiguration.Type.Should().Be(_componentResolver.Resolve(_components["X"]));
			componentConfiguration.FieldValues.Should().HaveCount(1);
			componentConfiguration.FieldValues[0].Values.Should().BeEquivalentTo(1, 2, 3, 4, 5, 6);
		}
	}
}