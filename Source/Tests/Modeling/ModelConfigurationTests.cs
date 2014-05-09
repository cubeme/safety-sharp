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

namespace Tests.Modeling
{
	using System;

	namespace ModelConfigurationTests
	{
		using System.Linq;
		using FluentAssertions;
		using NUnit.Framework;
		using SafetySharp.Modeling;
		using SafetySharp.Utilities;

		internal class ModelConfigurationTests
		{
			[UsedImplicitly(ImplicitUseTargetFlags.Members)]
			protected class ComplexComponent : Component
			{
				private Component _nested1;
				private Component _nested2;
				private object _other;

				public ComplexComponent(Component nested1, Component nested2, object other)
				{
					_nested1 = nested1;
					_nested2 = nested2;
					_other = other;
				}
			}

			protected class EmptyComponent : Component
			{
			}

			[UsedImplicitly(ImplicitUseTargetFlags.Members)]
			protected class NestedComponent : Component
			{
				private Component _nested;

				public NestedComponent(Component nested)
				{
					_nested = nested;
				}
			}

			protected class TestModelConfiguration : ModelConfiguration
			{
				public TestModelConfiguration(params Component[] rootComponents)
				{
					AddPartitions(rootComponents);
				}
			}
		}

		[TestFixture]
		internal class ComponentsProperty : ModelConfigurationTests
		{
			[Test]
			public void IgnoresNonComponentNullObjects()
			{
				var component1 = new EmptyComponent();
				var component2 = new EmptyComponent();
				var component3 = new ComplexComponent(component1, component2, null);
				var configuration = new TestModelConfiguration(component3).GetSnapshot();

				configuration.Components.Select(c => c.Component).Should().BeEquivalentTo(component1, component2, component3);
			}

			[Test]
			public void IgnoresNonComponentObjects()
			{
				var component1 = new EmptyComponent();
				var component2 = new EmptyComponent();
				var component3 = new ComplexComponent(component1, component2, new object());
				var configuration = new TestModelConfiguration(component3).GetSnapshot();

				configuration.Components.Select(c => c.Component).Should().BeEquivalentTo(component1, component2, component3);
			}

			[Test]
			public void IgnoresNullComponents()
			{
				var component = new NestedComponent(null);
				var configuration = new TestModelConfiguration(component).GetSnapshot();

				configuration.Components.Select(c => c.Component).Should().BeEquivalentTo(component);
			}

			[Test]
			public void ReturnsAllComponentsOfComplexHierarchy()
			{
				var component1 = new EmptyComponent();
				var component2 = new EmptyComponent();
				var component3 = new NestedComponent(component2);
				var component4 = new ComplexComponent(component1, component3, new object());
				var component5 = new EmptyComponent();
				var component6 = new ComplexComponent(component4, component5, new object());
				var configuration = new TestModelConfiguration(component6).GetSnapshot();

				configuration.Components.Select(c => c.Component)
							 .Should()
							 .BeEquivalentTo(component1, component2, component3, component4, component5, component6);
			}

			[Test]
			public void ReturnsAllComponentsOfLinearHierarchyWithFourLevels()
			{
				var component1 = new EmptyComponent();
				var component2 = new NestedComponent(component1);
				var component3 = new NestedComponent(component2);
				var component4 = new NestedComponent(component3);
				var configuration = new TestModelConfiguration(component4).GetSnapshot();

				configuration.Components.Select(c => c.Component).Should().BeEquivalentTo(component1, component2, component3, component4);
			}

			[Test]
			public void ReturnsAllComponentsOfLinearHierarchyWithTwoLevels()
			{
				var component1 = new EmptyComponent();
				var component2 = new NestedComponent(component1);
				var configuration = new TestModelConfiguration(component2).GetSnapshot();

				configuration.Components.Select(c => c.Component).Should().BeEquivalentTo(component1, component2);
			}

			[Test]
			public void ReturnsPartitionRoots()
			{
				var component1 = new EmptyComponent();
				var component2 = new EmptyComponent();
				var configuration = new TestModelConfiguration(component1, component2).GetSnapshot();

				configuration.Components.Select(c => c.Component).Should().BeEquivalentTo(component1, component2);
			}
		}

		[TestFixture]
		internal class GetSnapshot : ModelConfigurationTests
		{
			[Test]
			public void ThrowsWhenComponentsAreSharedBetweenDifferentRoots()
			{
				var component1 = new EmptyComponent();
				var component2 = new EmptyComponent();
				var component3 = new NestedComponent(component2);
				var component4 = new ComplexComponent(component1, component3, new object());
				var component5 = new EmptyComponent();
				var component6 = new ComplexComponent(component5, component2, new object());
				var configuration = new TestModelConfiguration(component4, component6);

				Action action = () => configuration.GetSnapshot();
				action.ShouldThrow<InvalidOperationException>();
			}

			[Test]
			public void ThrowsWhenComponentsAreSharedWithinSameRootAtDifferentLevels()
			{
				var component1 = new EmptyComponent();
				var component2 = new EmptyComponent();
				var component3 = new NestedComponent(component2);
				var component4 = new ComplexComponent(component1, component3, new object());
				var component5 = new ComplexComponent(component4, component2, new object());
				var configuration = new TestModelConfiguration(component5);

				Action action = () => configuration.GetSnapshot();
				action.ShouldThrow<InvalidOperationException>();
			}

			[Test]
			public void ThrowsWhenComponentsAreSharedWithinSameRootAtSameLevel()
			{
				var component1 = new EmptyComponent();
				var component2 = new ComplexComponent(component1, component1, null);
				var configuration = new TestModelConfiguration(component2);

				Action action = () => configuration.GetSnapshot();
				action.ShouldThrow<InvalidOperationException>();
			}

			[Test]
			public void ThrowsWhenNoPartitionRootIsSet()
			{
				var configuration = new TestModelConfiguration();

				Action action = () => configuration.GetSnapshot();
				action.ShouldThrow<InvalidOperationException>();
			}
		}

		[TestFixture]
		internal class PartitionRootsProperty : ModelConfigurationTests
		{
			[Test]
			public void ContainsAllTopLevelComponents()
			{
				var component1 = new EmptyComponent();
				var component2 = new EmptyComponent();
				var component3 = new EmptyComponent();
				var configuration = new TestModelConfiguration(component1, component2, component3).GetSnapshot();

				configuration.PartitionRoots.Select(c => c.Component).Should().BeEquivalentTo(component1, component2, component3);
			}

			[Test]
			public void ContainsSingleTopLevelComponent()
			{
				var component = new EmptyComponent();
				var configuration = new TestModelConfiguration(component).GetSnapshot();

				configuration.PartitionRoots.Select(c => c.Component).Should().BeEquivalentTo(component);
			}

			[Test]
			public void DoesNotContainNestedComponents()
			{
				var component1 = new EmptyComponent();
				var component2 = new NestedComponent(component1);
				var configuration = new TestModelConfiguration(component2).GetSnapshot();

				configuration.PartitionRoots.Select(c => c.Component).Should().BeEquivalentTo(component2);
			}
		}
	}
}