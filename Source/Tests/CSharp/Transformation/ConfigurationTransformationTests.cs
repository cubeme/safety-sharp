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

	namespace ConfigurationTransformationTests
	{
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
		using SafetySharp.Utilities;

		internal class ConfigurationTransformationTests
		{
			private ComponentResolver _componentResolver;
			private Dictionary<Component, IMetamodelReference<ComponentDeclaration>> _mappedComponents;
			private MetamodelResolver _metamodelResolver;

			private IMetamodelReference<ComponentDeclaration> CreateComponentDeclaration(Component component)
			{
				IMetamodelReference<ComponentDeclaration> reference;
				if (_mappedComponents.TryGetValue(component, out reference))
					return reference;

				var fields = ImmutableArray<FieldDeclaration>.Empty;
				var subComponents = ImmutableArray<SubComponentDeclaration>.Empty;

				foreach (var field in component.GetType().GetFields(BindingFlags.NonPublic | BindingFlags.Instance))
				{
					if (typeof(IComponent).IsAssignableFrom(field.FieldType))
					{
						var subComponent = CreateComponentDeclaration((Component)field.GetValue(component));
						subComponents = subComponents.Add(new SubComponentDeclaration(new Identifier(field.Name), subComponent));
					}
					else
					{
						var fieldType = field.FieldType == typeof(bool) ? (TypeSymbol)TypeSymbol.Boolean : TypeSymbol.Integer;
						fields = fields.Add(new FieldDeclaration(new Identifier(field.Name), fieldType));
					}
				}

				var componentDeclaration = ComponentDeclaration
					.Empty
					.WithIdentifier(new Identifier(component.GetType().FullName))
					.WithFields(fields)
					.WithSubComponents(subComponents);

				reference = new MetamodelReference<ComponentDeclaration>(component);
				_componentResolver = _componentResolver.With(component, reference);
				_metamodelResolver = _metamodelResolver.With(reference, componentDeclaration);

				_mappedComponents.Add(component, reference);
				return reference;
			}

			protected MetamodelConfiguration TransformConfiguration(params Component[] partitionRoots)
			{
				var configuration = new TestConfiguration(partitionRoots);
				_componentResolver = ComponentResolver.Empty;
				_metamodelResolver = MetamodelResolver.Empty;

				_mappedComponents = new Dictionary<Component, IMetamodelReference<ComponentDeclaration>>();
				foreach (var component in partitionRoots)
					CreateComponentDeclaration(component);

				var configurationTransformation = new ConfigurationTransformation(configuration, _metamodelResolver, _componentResolver);
				return configurationTransformation.Transform();
			}

			protected ComponentConfiguration CreateComponentConfiguration(Component component)
			{
				return new ComponentConfiguration(
					Identifier.Unknown,
					_componentResolver.Resolve(component),
					ImmutableArray<ValueArray>.Empty,
					ImmutableArray<ComponentConfiguration>.Empty);
			}

			[UsedImplicitly(ImplicitUseTargetFlags.Members)]
			protected class ComponentWithOneChild : Component
			{
				private Component _test;

				public ComponentWithOneChild(Component test)
				{
					_test = test;
				}
			}

			[UsedImplicitly(ImplicitUseTargetFlags.Members)]
			protected class ComponentWithTwoChildren : Component
			{
				private Component _test1;
				private Component _test2;

				public ComponentWithTwoChildren(Component test1, Component test2)
				{
					_test1 = test1;
					_test2 = test2;
				}
			}

			protected class TestComponent : Component
			{
			}

			private class TestConfiguration : ModelConfiguration
			{
				public TestConfiguration(Component[] components)
				{
					AddPartitions(components);
				}
			}
		}

		[TestFixture]
		internal class InitialValues : ConfigurationTransformationTests
		{
			private class ValueComponent<T> : Component
			{
				private readonly T _field = default(T);

				public ValueComponent(T[] values)
				{
					SetInitialValues(() => _field, values);
				}
			}

			private void CheckInitialValues<T>(params T[] values)
			{
				var metamodelConfiguration = TransformConfiguration(new ValueComponent<T>(values));
				var componentConfiguration = metamodelConfiguration.Partitions[0].Component;

				componentConfiguration.FieldValues[0].Values.Select(value => value.Object).ShouldBeEquivalentTo(values);
			}

			[Test]
			public void MultipleInitialValues()
			{
				CheckInitialValues(true, false);
				CheckInitialValues(1, 0);
				CheckInitialValues(-17, 77, -1);
				CheckInitialValues(427, 23, 412, 43, 20, 987453);
			}

			[Test]
			public void SingleInitialValue()
			{
				CheckInitialValues(true);
				CheckInitialValues(false);
				CheckInitialValues(0);
				CheckInitialValues(-17);
				CheckInitialValues(987453);
			}
		}

		[TestFixture]
		internal class Partitions : ConfigurationTransformationTests
		{
			[Test]
			public void MultiplePartitions()
			{
				var component1 = new TestComponent();
				var component2 = new TestComponent();

				TransformConfiguration(component1, component2)
					.Partitions.Should().BeEquivalentTo(
						new Partition(CreateComponentConfiguration(component1)),
						new Partition(CreateComponentConfiguration(component2)));
			}

			[Test]
			public void SinglePartition()
			{
				var component = new TestComponent();
				TransformConfiguration(component)
					.Partitions.Should().BeEquivalentTo(new Partition(CreateComponentConfiguration(component)));
			}

			[Test]
			public void SubComponentIsNotPartitionRoot()
			{
				var component1 = new TestComponent();
				var component2 = new ComponentWithOneChild(component1);

				TransformConfiguration(component2)
					.Partitions.Should().BeEquivalentTo(
						new Partition(CreateComponentConfiguration(component2)
										  .WithSubComponents(ImmutableArray.Create(CreateComponentConfiguration(component1)))));
			}

			[Test]
			public void ThrowsWhenPartitionRootsAreShared()
			{
				var component = new TestComponent();

				Action action = () => TransformConfiguration(component, component);
				action.ShouldThrow<InvalidOperationException>();
			}
		}

		[TestFixture]
		internal class SubComponents : ConfigurationTransformationTests
		{
			[Test]
			public void DeeplyNestedComponents()
			{
				var component1 = new TestComponent();
				var component2 = new TestComponent();
				var component3 = new TestComponent();
				var component4 = new TestComponent();
				var component5 = new ComponentWithTwoChildren(component2, component1);
				var component6 = new ComponentWithTwoChildren(component5, component3);
				var component7 = new ComponentWithTwoChildren(component6, component4);
				var component8 = new ComponentWithOneChild(component7);

				TransformConfiguration(component8).Partitions.Should().BeEquivalentTo(
					new Partition(CreateComponentConfiguration(component8)
									  .WithSubComponents(ImmutableArray.Create(
										  CreateComponentConfiguration(component7)
											  .WithSubComponents(ImmutableArray.Create(
												  CreateComponentConfiguration(component6)
													  .WithSubComponents(ImmutableArray.Create(
														  CreateComponentConfiguration(component5)
															  .WithSubComponents(ImmutableArray.Create(
																  CreateComponentConfiguration(component2),
																  CreateComponentConfiguration(component1))),
														  CreateComponentConfiguration(component3))),
												  CreateComponentConfiguration(component4)))))));
			}

			[Test]
			public void DeeplyNestedComponentsInMultiplePartitions()
			{
				var component1 = new TestComponent();
				var component2 = new TestComponent();
				var component3 = new TestComponent();
				var component4 = new TestComponent();
				var component5 = new ComponentWithTwoChildren(component2, component1);
				var component6 = new ComponentWithTwoChildren(component5, component3);
				var component7 = new ComponentWithTwoChildren(component6, component4);
				var component8 = new ComponentWithOneChild(component7);
				var component9 = new TestComponent();
				var component10 = new TestComponent();
				var component11 = new TestComponent();
				var component12 = new TestComponent();
				var component13 = new ComponentWithOneChild(component9);
				var component14 = new ComponentWithTwoChildren(component10, component11);
				var component15 = new ComponentWithTwoChildren(component12, component13);

				TransformConfiguration(component8, component14, component15)
					.Partitions.Should().BeEquivalentTo(
						new Partition(CreateComponentConfiguration(component8)
										  .WithSubComponents(ImmutableArray.Create(
											  CreateComponentConfiguration(component7)
												  .WithSubComponents(ImmutableArray.Create(
													  CreateComponentConfiguration(component6)
														  .WithSubComponents(ImmutableArray.Create(
															  CreateComponentConfiguration(component5)
																  .WithSubComponents(ImmutableArray.Create(
																	  CreateComponentConfiguration(component2),
																	  CreateComponentConfiguration(component1))),
															  CreateComponentConfiguration(component3))),
													  CreateComponentConfiguration(component4)))))),
						new Partition(CreateComponentConfiguration(component14)
										  .WithSubComponents(ImmutableArray.Create(
											  CreateComponentConfiguration(component10),
											  CreateComponentConfiguration(component11)))),
						new Partition(CreateComponentConfiguration(component15)
										  .WithSubComponents(ImmutableArray.Create(
											  CreateComponentConfiguration(component12),
											  CreateComponentConfiguration(component13)
												  .WithSubComponents(ImmutableArray.Create(
													  CreateComponentConfiguration(component9)))))));
			}

			[Test]
			public void SingleSubComponent()
			{
				var component1 = new TestComponent();
				var component2 = new ComponentWithOneChild(component1);

				TransformConfiguration(component2)
					.Partitions[0].Component.Should().Be(
						CreateComponentConfiguration(component2)
							.WithSubComponents(ImmutableArray.Create(CreateComponentConfiguration(component1))));
			}

			[Test]
			public void ThrowsWhenSubComponentsAreSharedBetweenPartitions()
			{
				var component1 = new TestComponent();
				var component2 = new TestComponent();
				var component3 = new TestComponent();
				var component4 = new ComponentWithTwoChildren(component1, component2);
				var component5 = new ComponentWithTwoChildren(component1, component3);

				Action action = () => TransformConfiguration(component4, component5);
				action.ShouldThrow<InvalidOperationException>();
			}

			[Test]
			public void ThrowsWhenSubComponentsAreSharedWithinPartition()
			{
				var component1 = new TestComponent();
				var component2 = new ComponentWithTwoChildren(component1, component1);

				Action action = () => TransformConfiguration(component2);
				action.ShouldThrow<InvalidOperationException>();
			}

			[Test]
			public void TwoSubComponents()
			{
				var component1 = new TestComponent();
				var component2 = new TestComponent();
				var component3 = new ComponentWithTwoChildren(component1, component2);

				TransformConfiguration(component3)
					.Partitions[0].Component.Should().Be(
						CreateComponentConfiguration(component3)
							.WithSubComponents(ImmutableArray.Create(
								CreateComponentConfiguration(component1),
								CreateComponentConfiguration(component2))));
			}
		}
	}
}