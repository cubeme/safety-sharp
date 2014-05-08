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
	using System.Collections.Immutable;
	using System.Linq;
	using System.Reflection;
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.CSharp.Transformation;
	using SafetySharp.Metamodel;
	using SafetySharp.Metamodel.Declarations;
	using SafetySharp.Metamodel.Types;
	using SafetySharp.Modeling;

	[TestFixture]
	internal class ConfigurationTransformationTests
	{
		private class TestComponent<T> : Component
		{
			private readonly T _field = default(T);

			public TestComponent(params T[] values)
			{
				SetInitialValues(() => _field, values);
			}
		}

		private class TestConfiguration : ModelConfiguration
		{
			public TestConfiguration(params Component[] components)
			{
				AddPartitions(components);
			}
		}

		private ComponentResolver _componentResolver;
		private MetamodelResolver _metamodelResolver;

		private MetamodelConfiguration TransformConfiguration(ModelConfiguration configuration, params Component[] components)
		{
			_componentResolver = ComponentResolver.Empty;
			_metamodelResolver = MetamodelResolver.Empty;

			foreach (var component in components)
			{
				var fields = ImmutableArray<FieldDeclaration>.Empty;
				foreach (var field in component.GetType().GetFields(BindingFlags.NonPublic | BindingFlags.Instance))
				{
					var fieldType = field.FieldType == typeof(bool) ? (TypeSymbol)TypeSymbol.Boolean : TypeSymbol.Integer;
					fields = fields.Add(new FieldDeclaration(new Identifier(field.Name), fieldType));
				}

				var componentDeclaration = new ComponentDeclaration(
					new Identifier(component.GetType().FullName),
					MethodDeclaration.UpdateMethod,
					ImmutableArray<MethodDeclaration>.Empty,
					fields,
					ImmutableArray<SubComponentDeclaration>.Empty);

				var reference = new MetamodelReference<ComponentDeclaration>(component);
				_componentResolver = _componentResolver.With(component, reference);
				_metamodelResolver = _metamodelResolver.With(reference, componentDeclaration);
			}

			var configurationTransformation = new ConfigurationTransformation(configuration, _metamodelResolver, _componentResolver);
			return configurationTransformation.Transform();
		}

		private void CheckComponentTypes(IEnumerable<MetamodelReference<ComponentDeclaration>> declarations, params Component[] components)
		{
			declarations.Should().BeEquivalentTo(components.Select(_componentResolver.Resolve));
		}

		private void ShouldHaveInitialValues<T>(params T[] values)
		{
			var component = new TestComponent<T>(values);
			var configuration = new TestConfiguration(component);

			var metamodelConfiguration = TransformConfiguration(configuration, component);
			var componentConfiguration = metamodelConfiguration.Partitions[0].Component;
			componentConfiguration.FieldValues.Should().HaveCount(1);
			componentConfiguration.FieldValues[0].Values.Should().BeEquivalentTo(values);
		}

		[Test]
		public void ShouldHave_OnePartition()
		{
			var component = new TestComponent<int>(0);
			var configuration = new TestConfiguration(component);

			var metamodelConfiguration = TransformConfiguration(configuration, component);
			metamodelConfiguration.Partitions.Should().HaveCount(1);
			CheckComponentTypes(metamodelConfiguration.Partitions.Select(p => p.Component.Type), component);
		}

		[Test]
		public void ShouldHave_MultipleInitialValues_Int()
		{
			ShouldHaveInitialValues(1, 0);
			ShouldHaveInitialValues(-17, 77, -1);
			ShouldHaveInitialValues(427, 23, 412, 43, 20, 987453);
		}

		[Test]
		public void ShouldHave_MultipleInitialValues_Bool()
		{
			ShouldHaveInitialValues(true, false);
		}

		[Test]
		public void ShouldHave_SingleInitialValue_Bool()
		{
			ShouldHaveInitialValues(false);
			ShouldHaveInitialValues(true);
		}

		[Test]
		public void ShouldHave_SingleInitialValue_Int()
		{
			ShouldHaveInitialValues(1);
			ShouldHaveInitialValues(-17);
			ShouldHaveInitialValues(427);
		}

		[Test]
		public void ShouldHave_TwoPartitions()
		{
			var component1 = new TestComponent<int>(0);
			var component2 = new TestComponent<int>(0);
			var configuration = new TestConfiguration(component1, component2);

			var metamodelConfiguration = TransformConfiguration(configuration, component1, component2);
			metamodelConfiguration.Partitions.Should().HaveCount(2);
			CheckComponentTypes(metamodelConfiguration.Partitions.Select(p => p.Component.Type), component1, component2);
		}
	}
}