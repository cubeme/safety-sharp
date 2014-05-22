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

	namespace ComponentTests
	{
		using System.Linq;
		using System.Linq.Expressions;
		using FluentAssertions;
		using NUnit.Framework;
		using SafetySharp.Modeling;
		using SafetySharp.Utilities;

		internal class ComponentTests
		{
			[UsedImplicitly(ImplicitUseTargetFlags.Members)]
			protected class FieldComponent : Component
			{
				private int _field;

				public FieldComponent(int field = 0)
				{
					_field = field;
				}
			}

			[UsedImplicitly(ImplicitUseTargetFlags.Members)]
			protected class OneSubComponent : Component
			{
				private Component _component;

				public OneSubComponent(Component component)
				{
					_component = component;
				}
			}

			[UsedImplicitly(ImplicitUseTargetFlags.Members)]
			protected class TwoSubComponent : Component
			{
				private Component _component1;
				private Component _component2;

				public TwoSubComponent(Component component1, Component component2)
				{
					_component1 = component1;
					_component2 = component2;
				}
			}
		}

		[TestFixture]
		internal class SetInitialValuesMethod
		{
			[UsedImplicitly(ImplicitUseTargetFlags.Members)]
			private class TestComponent<T> : Component
			{
				private T _field = default(T);

				public TestComponent(params T[] values)
				{
					SetInitialValues(() => _field, false, values);
				}
			}

			[UsedImplicitly(ImplicitUseTargetFlags.Members)]
			private class TestComponent : Component
			{
				public int Field = 17;

				public TestComponent(bool setValue, params int[] values)
				{
					SetInitialValues(() => Field, setValue, values);
				}
			}

			private class ExpressionComponent : Component
			{
				public ExpressionComponent(Expression<Func<int>> expression)
				{
					SetInitialValues(expression, false, 1);
				}
			}

			[Test]
			public void ShouldNotSetFieldValueIfNotRequested()
			{
				var component = new TestComponent(false, 1, 2);
				component.Field.Should().Be(17);
			}

			[Test]
			public void ShouldSetFieldValueIfRequested()
			{
				var component = new TestComponent(true, 3);
				component.Field.Should().Be(3);

				component = new TestComponent(true, 3, 182);
				(component.Field == 3 || component.Field == 182).Should().BeTrue();
			}

			[Test]
			public void ThrowsWhenExpressionDoesNotReferenceField()
			{
				Action action = () => new ExpressionComponent(() => 1 + 1);
				action.ShouldThrow<ArgumentException>();

				const int i = 0;
				action = () => new ExpressionComponent(() => i);
				action.ShouldThrow<ArgumentException>();
			}

			[Test]
			public void ThrowsWhenFieldExpressionIsNull()
			{
				Action action = () => new ExpressionComponent(null);
				action.ShouldThrow<ArgumentNullException>();
			}

			[Test]
			public void ThrowsWhenInitialValuesIsEmpty()
			{
				Action action = () => new TestComponent<int>();
				action.ShouldThrow<ArgumentException>();
			}

			[Test]
			public void ThrowsWhenInitialValuesIsNull()
			{
				Action action = () => new TestComponent<int>(null);
				action.ShouldThrow<ArgumentNullException>();
			}
		}

		[TestFixture]
		internal class GetInitialValuesOfFieldMethod : ComponentTests
		{
			[UsedImplicitly(ImplicitUseTargetFlags.Members)]
			private class TestComponent<T> : Component
			{
				private T _field;

				public TestComponent(params T[] values)
				{
					_field = values[0];
					SetInitialValues(() => _field, false, values);
				}
			}

			[UsedImplicitly(ImplicitUseTargetFlags.Members)]
			private class TestComponent<T1, T2> : Component
			{
				private T1 _field1;
				private T2 _field2;

				public TestComponent(T1[] values1, T2[] values2)
				{
					_field1 = values1[0];
					_field2 = values2[0];

					SetInitialValues(() => _field1, false, values1);
					SetInitialValues(() => _field2, false, values2);
				}
			}

			[Test]
			public void ReturnsInitialValuesOfSingleKnownField()
			{
				var integerComponent = new TestComponent<int>(17).GetSnapshot();
				integerComponent.GetInitialValuesOfField("_field").Should().BeEquivalentTo(17);

				integerComponent = new TestComponent<int>(17, 0, -33).GetSnapshot();
				integerComponent.GetInitialValuesOfField("_field").Should().BeEquivalentTo(17, 0, -33);

				var booleanComponent = new TestComponent<bool>(true).GetSnapshot();
				booleanComponent.GetInitialValuesOfField("_field").Should().BeEquivalentTo(true);

				booleanComponent = new TestComponent<bool>(true, false).GetSnapshot();
				booleanComponent.GetInitialValuesOfField("_field").Should().BeEquivalentTo(true, false);
			}

			[Test]
			public void ReturnsInitialValuesofMultipleKnownFields()
			{
				var intValues = new[] { 142, 874, 11 };
				var boolValues = new[] { true, false };
				var component = new TestComponent<int, bool>(intValues, boolValues).GetSnapshot();

				component.GetInitialValuesOfField("_field1").Should().BeEquivalentTo(intValues);
				component.GetInitialValuesOfField("_field2").Should().BeEquivalentTo(boolValues);
			}

			[Test]
			public void ThrowsForSubComponentField()
			{
				var component = new OneSubComponent(new FieldComponent()).GetSnapshot();

				Action action = () => component.GetInitialValuesOfField("_component");
				action.ShouldThrow<ArgumentException>();
			}

			[Test]
			public void ThrowsForUnknownField()
			{
				var component = new TestComponent<int>(0).GetSnapshot();

				Action action = () => component.GetInitialValuesOfField("x");
				action.ShouldThrow<ArgumentException>();
			}

			[Test]
			public void ThrowsWhenEmptyStringIsPassed()
			{
				var component = new TestComponent<int>(0).GetSnapshot();

				Action action = () => component.GetInitialValuesOfField(String.Empty);
				action.ShouldThrow<ArgumentException>();
			}

			[Test]
			public void ThrowsWhenNullIsPassed()
			{
				var component = new TestComponent<int>(0).GetSnapshot();

				Action action = () => component.GetInitialValuesOfField(null);
				action.ShouldThrow<ArgumentNullException>();
			}
		}

		[TestFixture]
		internal class GetSubComponentMethod : ComponentTests
		{
			[Test]
			public void ReturnsMultipleSubComponents()
			{
				var subComponent1 = new FieldComponent();
				var subComponent2 = new FieldComponent();
				var component = new TwoSubComponent(subComponent1, subComponent2).GetSnapshot();

				component.GetSubComponent("_component1").Component.Should().Be(subComponent1);
				component.GetSubComponent("_component2").Component.Should().Be(subComponent2);
			}

			[Test]
			public void ReturnsSingleSubComponent()
			{
				var subComponent = new FieldComponent();
				var component = new OneSubComponent(subComponent).GetSnapshot();

				component.GetSubComponent("_component").Component.Should().Be(subComponent);
			}

			[Test]
			public void ThrowsForNonComponentField()
			{
				var component = new FieldComponent().GetSnapshot();

				Action action = () => component.GetSubComponent("_field");
				action.ShouldThrow<ArgumentException>();
			}

			[Test]
			public void ThrowsForUnknownComponentField()
			{
				var component = new OneSubComponent(new FieldComponent()).GetSnapshot();

				Action action = () => component.GetSubComponent("_field");
				action.ShouldThrow<ArgumentException>();
			}

			[Test]
			public void ThrowsWhenEmptyStringIsPassed()
			{
				var component = new OneSubComponent(new FieldComponent()).GetSnapshot();

				Action action = () => component.GetSubComponent(String.Empty);
				action.ShouldThrow<ArgumentException>();
			}

			[Test]
			public void ThrowsWhenNullIsPassed()
			{
				var component = new OneSubComponent(new FieldComponent()).GetSnapshot();

				Action action = () => component.GetSubComponent(null);
				action.ShouldThrow<ArgumentNullException>();
			}
		}

		[TestFixture]
		internal class SubComponentsProperty : ComponentTests
		{
			private class TestComponent : Component
			{
			}

			[Test]
			public void IgnoresNonSubComponentFields()
			{
				var component = new FieldComponent();
				component.SubComponents.Should().BeEmpty();

				var snapshot = component.GetSnapshot();
				snapshot.SubComponents.Should().BeEmpty();
			}

			[Test]
			public void IgnoresNullSubComponents()
			{
				var component = new OneSubComponent(null);
				component.SubComponents.Should().BeEmpty();

				var snapshot = component.GetSnapshot();
				snapshot.SubComponents.Should().BeEmpty();
			}

			[Test]
			public void ReturnsMultipleSubComponents()
			{
				var subComponent1 = new TestComponent();
				var subComponent2 = new FieldComponent();
				var component = new TwoSubComponent(subComponent1, subComponent2);

				component.SubComponents.Should().BeEquivalentTo(subComponent1, subComponent2);

				var snapshot = component.GetSnapshot();
				snapshot.SubComponents.Select(c => c.Component).Should().BeEquivalentTo(subComponent1, subComponent2);
			}

			[Test]
			public void ReturnsNoneIfComponentHasNoSubComponents()
			{
				var component = new TestComponent();
				component.SubComponents.Should().BeEmpty();

				var snapshot = component.GetSnapshot();
				snapshot.SubComponents.Should().BeEmpty();
			}

			[Test]
			public void ReturnsSingleSubComponent()
			{
				var subComponent = new TestComponent();
				var component = new OneSubComponent(subComponent);

				component.SubComponents.Should().BeEquivalentTo(subComponent);

				var snapshot = component.GetSnapshot();
				snapshot.SubComponents.Select(c => c.Component).Should().BeEquivalentTo(subComponent);
			}
		}
	}
}