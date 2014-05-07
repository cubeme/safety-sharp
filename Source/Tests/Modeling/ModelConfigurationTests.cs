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
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.Modeling;

	[TestFixture]
	internal class ModelConfigurationTests
	{
		private class EmptyComponent : Component
		{
		}

		private class NestedComponent : Component
		{
			private Component _nested;

			public NestedComponent(Component nested)
			{
				_nested = nested;
			}
		}

		private class ComplexComponent : Component
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

		private class TestModelConfiguration : ModelConfiguration
		{
			public TestModelConfiguration(params Component[] rootComponents)
			{
				AddPartitions(rootComponents);
			}
		}

		[Test]
		public void ComponentsProperty_ShouldContain_AllComponentsOfComplexHierarchy()
		{
			var component1 = new EmptyComponent();
			var component2 = new EmptyComponent();
			var component3 = new NestedComponent(component2);
			var component4 = new ComplexComponent(component1, component3, new object());
			var component5 = new EmptyComponent();
			var component6 = new ComplexComponent(component4, component5, new object());
			var config = new TestModelConfiguration(component6);
			var components = config.GetComponents();

			components.Should().HaveCount(6);
			components.Should().Contain(component1);
			components.Should().Contain(component2);
			components.Should().Contain(component3);
			components.Should().Contain(component4);
			components.Should().Contain(component5);
			components.Should().Contain(component6);
		}

		[Test]
		public void ComponentsProperty_ShouldContain_MultipleNestedComponents_NullOtherObject()
		{
			var component1 = new EmptyComponent();
			var component2 = new EmptyComponent();
			var component3 = new ComplexComponent(component1, component2, null);
			var config = new TestModelConfiguration(component3);
			var components = config.GetComponents();

			components.Should().HaveCount(3);
			components.Should().Contain(component1);
			components.Should().Contain(component2);
			components.Should().Contain(component3);
		}

		[Test]
		public void ComponentsProperty_ShouldContain_NestedComponents_FourLevels()
		{
			var component1 = new EmptyComponent();
			var component2 = new NestedComponent(component1);
			var component3 = new NestedComponent(component2);
			var component4 = new NestedComponent(component3);
			var config = new TestModelConfiguration(component4);
			var components = config.GetComponents();

			components.Should().HaveCount(4);
			components.Should().Contain(component1);
			components.Should().Contain(component2);
			components.Should().Contain(component3);
			components.Should().Contain(component4);
		}

		[Test]
		public void ComponentsProperty_ShouldContain_NestedComponents_TwoLevels()
		{
			var component1 = new EmptyComponent();
			var component2 = new NestedComponent(component1);
			var config = new TestModelConfiguration(component2);
			var components = config.GetComponents();

			components.Should().HaveCount(2);
			components.Should().Contain(component1);
			components.Should().Contain(component2);
		}

		[Test]
		public void ComponentsProperty_ShouldContain_PartitionRoots()
		{
			var component1 = new EmptyComponent();
			var component2 = new EmptyComponent();
			var config = new TestModelConfiguration(component1, component2);
			var components = config.GetComponents();

			components.Should().HaveCount(2);
			components[0].Should().Be(component1);
			components[1].Should().Be(component2);
		}

		[Test]
		public void ComponentsProperty_ShouldNotContain_NestedNullComponents()
		{
			var component = new NestedComponent(null);
			var config = new TestModelConfiguration(component);
			var components = config.GetComponents();

			components.Should().HaveCount(1);
			components.Should().Contain(component);
		}

		[Test]
		public void ComponentsProperty_ShouldNotContain_OtherObject()
		{
			var component1 = new EmptyComponent();
			var component2 = new EmptyComponent();
			var component3 = new ComplexComponent(component1, component2, new object());
			var config = new TestModelConfiguration(component3);
			var components = config.GetComponents();

			components.Should().HaveCount(3);
			components.Should().Contain(component1);
			components.Should().Contain(component2);
			components.Should().Contain(component3);
		}

		[Test]
		public void PartitionRootsProperty_ShouldContain_TopLevelComponents()
		{
			var component1 = new EmptyComponent();
			var component2 = new EmptyComponent();
			var component3 = new EmptyComponent();
			var config = new TestModelConfiguration(component1, component2, component3);

			config.PartitionRoots.Should().HaveCount(3);
			config.PartitionRoots[0].Should().Be(component1);
			config.PartitionRoots[1].Should().Be(component2);
			config.PartitionRoots[2].Should().Be(component3);
		}

		[Test]
		public void PartitionRootsProperty_ShouldNotContain_NestedComponents()
		{
			var component1 = new EmptyComponent();
			var component2 = new NestedComponent(component1);
			var config = new TestModelConfiguration(component2);

			config.PartitionRoots.Should().HaveCount(1);
			config.PartitionRoots[0].Should().Be(component2);
		}

		[Test]
		public void Transform_ShouldThrow_NoPartitions()
		{
			var config = new TestModelConfiguration();
			Action action = () => config.GetComponents();

			action.ShouldThrow<InvalidOperationException>();
		}

		[Test]
		public void Transform_ShouldThrow_SharedComponent_DifferentLevels()
		{
			var component1 = new EmptyComponent();
			var component2 = new EmptyComponent();
			var component3 = new NestedComponent(component2);
			var component4 = new ComplexComponent(component1, component3, new object());
			var component5 = new ComplexComponent(component4, component2, new object());
			var config = new TestModelConfiguration(component5);

			Action action = () => config.GetComponents();
			action.ShouldThrow<InvalidOperationException>();
		}

		[Test]
		public void Transform_ShouldThrow_SharedComponent_DifferentRoots()
		{
			var component1 = new EmptyComponent();
			var component2 = new EmptyComponent();
			var component3 = new NestedComponent(component2);
			var component4 = new ComplexComponent(component1, component3, new object());
			var component5 = new EmptyComponent();
			var component6 = new ComplexComponent(component5, component2, new object());
			var config = new TestModelConfiguration(component4, component6);

			Action action = () => config.GetComponents();
			action.ShouldThrow<InvalidOperationException>();
		}

		[Test]
		public void Transform_ShouldThrow_SharedComponent_SameLevel()
		{
			var component1 = new EmptyComponent();
			var component2 = new ComplexComponent(component1, component1, null);
			var config = new TestModelConfiguration(component2);

			Action action = () => config.GetComponents();
			action.ShouldThrow<InvalidOperationException>();
		}
	}
}