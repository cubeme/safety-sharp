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
	using SafetySharp.Metamodel.Configurations;
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

		private class NestedComponent<T> : Component
		{
			private TestComponent<T> _test;

			public NestedComponent(TestComponent<T> test)
			{
				_test = test;
			}
		}

		private class TwoNestedComponent<T1, T2> : Component
		{
			private TestComponent<T1> _test1;
			private TestComponent<T2> _test2;

			public TwoNestedComponent(TestComponent<T1> test1, TestComponent<T2> test2)
			{
				_test1 = test1;
				_test2 = test2;
			}
		}

		private interface IDeeplyNestedComponent : IComponent
		{
		}

		private class DeeplyNestedLeafComponent : Component, IDeeplyNestedComponent
		{
		}

		private class DeeplyNestedComponent : Component, IDeeplyNestedComponent
		{
			private IDeeplyNestedComponent _test1;
			private IDeeplyNestedComponent _test2;

			public DeeplyNestedComponent(IDeeplyNestedComponent test1, IDeeplyNestedComponent test2)
			{
				_test1 = test1;
				_test2 = test2;
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

		private MetamodelReference<ComponentDeclaration> CreateComponentDeclaration(IComponent component)
		{
			var fields = ImmutableArray<FieldDeclaration>.Empty;
			var subComponents = ImmutableArray<SubComponentDeclaration>.Empty;

			foreach (var field in component.GetType().GetFields(BindingFlags.NonPublic | BindingFlags.Instance))
			{
				if (typeof(IComponent).IsAssignableFrom(field.FieldType))
				{
					var subComponent = CreateComponentDeclaration((IComponent)field.GetValue(component));
					subComponents = subComponents.Add(new SubComponentDeclaration(new Identifier(field.Name), subComponent));
				}
				else
				{
					var fieldType = field.FieldType == typeof(bool) ? (TypeSymbol)TypeSymbol.Boolean : TypeSymbol.Integer;
					fields = fields.Add(new FieldDeclaration(new Identifier(field.Name), fieldType));
				}
			}

			var componentDeclaration = new ComponentDeclaration(
				new Identifier(component.GetType().FullName),
				MethodDeclaration.UpdateMethod,
				ImmutableArray<MethodDeclaration>.Empty,
				fields,
				subComponents);

			var reference = new MetamodelReference<ComponentDeclaration>(component);
			_componentResolver = _componentResolver.With(component, reference);
			_metamodelResolver = _metamodelResolver.With(reference, componentDeclaration);

			return reference;
		}

		private MetamodelConfiguration TransformConfiguration(ModelConfiguration configuration, params Component[] rootComponents)
		{
			_componentResolver = ComponentResolver.Empty;
			_metamodelResolver = MetamodelResolver.Empty;

			foreach (var component in rootComponents)
				CreateComponentDeclaration(component);

			var configurationTransformation = new ConfigurationTransformation(configuration, _metamodelResolver, _componentResolver);
			return configurationTransformation.Transform();
		}

		private void CheckComponentTypes(IEnumerable<IMetamodelReference<ComponentDeclaration>> declarations, params Component[] components)
		{
			declarations.Should().BeEquivalentTo(components.Select(_componentResolver.Resolve));
		}

		private void CheckComponentType(IMetamodelReference<ComponentDeclaration> declaration, Component component)
		{
			declaration.Should().Be(_componentResolver.Resolve(component));
		}

		private void ShouldHaveInitialValues<T>(params T[] values)
		{
			var initialValues = values.Select(value => new Value(value));
			var component = new TestComponent<T>(values);
			var configuration = new TestConfiguration(component);

			var metamodelConfiguration = TransformConfiguration(configuration, component);
			var componentConfiguration = metamodelConfiguration.Partitions[0].Component;
			componentConfiguration.FieldValues.Should().HaveCount(1);
			componentConfiguration.FieldValues[0].Values.Should().BeEquivalentTo(initialValues);
		}

		[Test]
		public void MultipleInitialValues_Bool()
		{
			ShouldHaveInitialValues(true, false);
		}

		[Test]
		public void MultipleInitialValues_Int()
		{
			ShouldHaveInitialValues(1, 0);
			ShouldHaveInitialValues(-17, 77, -1);
			ShouldHaveInitialValues(427, 23, 412, 43, 20, 987453);
		}

		[Test]
		public void DeeplyNestedComponents()
		{
			var component1 = new DeeplyNestedLeafComponent();
			var component2 = new DeeplyNestedLeafComponent();
			var component3 = new DeeplyNestedLeafComponent();
			var component4 = new DeeplyNestedLeafComponent();
			var component5 = new DeeplyNestedComponent(component2, component1);
			var component6 = new DeeplyNestedComponent(component5, component3);
			var component7 = new DeeplyNestedComponent(component6, component4);
			var configuration = new TestConfiguration(component7);

			var metamodelConfiguration = TransformConfiguration(configuration, component7);

			var c7 = metamodelConfiguration.Partitions[0].Component;
			CheckComponentType(c7.Type, component7);

			c7.SubComponents.Should().HaveCount(2);
			CheckComponentType(c7.SubComponents[0].Type, component6);
			CheckComponentType(c7.SubComponents[1].Type, component4);

			var c6 = c7.SubComponents[0];
			var c4 = c7.SubComponents[1];

			c4.SubComponents.Should().HaveCount(0);
			c6.SubComponents.Should().HaveCount(2);
			CheckComponentType(c6.SubComponents[0].Type, component5);
			CheckComponentType(c6.SubComponents[1].Type, component3);

			var c5 = c6.SubComponents[0];
			var c3 = c6.SubComponents[1];

			c3.SubComponents.Should().HaveCount(0);
			c5.SubComponents.Should().HaveCount(2);
			CheckComponentType(c5.SubComponents[0].Type, component2);
			CheckComponentType(c5.SubComponents[1].Type, component1);

			var c2 = c5.SubComponents[0];
			var c1 = c5.SubComponents[1];

			c1.SubComponents.Should().HaveCount(0);
			c2.SubComponents.Should().HaveCount(0);
		}

		[Test]
		public void OnePartition()
		{
			var component = new TestComponent<int>(0);
			var configuration = new TestConfiguration(component);

			var metamodelConfiguration = TransformConfiguration(configuration, component);
			metamodelConfiguration.Partitions.Should().HaveCount(1);
			CheckComponentTypes(metamodelConfiguration.Partitions.Select(p => p.Component.Type), component);
		}

		[Test]
		public void SingleInitialValue_Bool()
		{
			ShouldHaveInitialValues(false);
			ShouldHaveInitialValues(true);
		}

		[Test]
		public void SingleInitialValue_Int()
		{
			ShouldHaveInitialValues(1);
			ShouldHaveInitialValues(-17);
			ShouldHaveInitialValues(427);
		}

		[Test]
		public void SingleSubComponent()
		{
			var component1 = new TestComponent<int>(24, 12);
			var component2 = new NestedComponent<int>(component1);
			var configuration = new TestConfiguration(component2);

			var metamodelConfiguration = TransformConfiguration(configuration, component2);
			var component = metamodelConfiguration.Partitions[0].Component;
			CheckComponentType(component.Type, component2);

			component.SubComponents.Should().HaveCount(1);
			CheckComponentType(component.SubComponents[0].Type, component1);
		}

		[Test]
		public void TwoPartitions()
		{
			var component1 = new TestComponent<int>(0);
			var component2 = new TestComponent<int>(0);
			var configuration = new TestConfiguration(component1, component2);

			var metamodelConfiguration = TransformConfiguration(configuration, component1, component2);
			metamodelConfiguration.Partitions.Should().HaveCount(2);
			CheckComponentTypes(metamodelConfiguration.Partitions.Select(p => p.Component.Type), component1, component2);
		}

		[Test]
		public void TwoSubComponents()
		{
			var component1 = new TestComponent<int>(24, 12);
			var component2 = new TestComponent<bool>(false);
			var component3 = new TwoNestedComponent<int, bool>(component1, component2);
			var configuration = new TestConfiguration(component3);

			var metamodelConfiguration = TransformConfiguration(configuration, component3);
			var component = metamodelConfiguration.Partitions[0].Component;
			CheckComponentType(component.Type, component3);

			component.SubComponents.Should().HaveCount(2);
			CheckComponentType(component.SubComponents[0].Type, component1);
			CheckComponentType(component.SubComponents[1].Type, component2);
		}
	}
}