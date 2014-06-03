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

	namespace ComponentSnapshotTests
	{
		using FluentAssertions;
		using NUnit.Framework;
		using SafetySharp.Modeling;
		using SafetySharp.Utilities;

		[TestFixture]
		internal class EqualityOperator
		{
			[UsedImplicitly(ImplicitUseTargetFlags.WithMembers)]
			private class FieldComponent : Component
			{
				public int Field;

				public FieldComponent(int field = 0)
				{
					Field = field;
				}
			}

			[UsedImplicitly(ImplicitUseTargetFlags.WithMembers)]
			private class SubComponent : Component
			{
				public Component Component;

				public SubComponent(Component component)
				{
					Component = component;
				}
			}

			[Test]
			public void ReturnsFalseForDifferentSnapshots()
			{
				var component1 = new FieldComponent(2);
				var component2 = new SubComponent(component1);

				component1.GetSnapshot().Equals(component2.GetSnapshot()).Should().BeFalse();
			}

			[Test]
			public void ReturnsTrueForSnapshotsWithDifferentNames()
			{
				var component = new FieldComponent(1);
				component.GetSnapshot().Equals(component.GetSnapshot("OtherName")).Should().BeTrue();
			}

			[Test]
			public void ReturnsFalseForSnapshotsFromDifferentState()
			{
				var component1 = new FieldComponent(2);
				var snapshot1 = component1.GetSnapshot();

				component1.Field = 7;
				snapshot1.Equals(component1.GetSnapshot()).Should().BeFalse();

				var component2 = new SubComponent(component1);
				var snapshot2 = component2.GetSnapshot();

				component2.Component = new FieldComponent(5);
				snapshot2.Equals(component2.GetSnapshot()).Should().BeFalse();
			}

			[Test]
			public void ReturnsTrueForDifferentSnapshotsFromSameState()
			{
				var component1 = new FieldComponent(2);
				var component2 = new SubComponent(component1);

				component1.GetSnapshot().Equals(component1.GetSnapshot()).Should().BeTrue();
				component2.GetSnapshot().Equals(component2.GetSnapshot()).Should().BeTrue();
			}

			[Test]
			public void ReturnsTrueForSameSnapshot()
			{
				var component1 = new FieldComponent(2);
				var component2 = new SubComponent(component1);
				var snapshot1 = component1.GetSnapshot();
				var snapshot2 = component2.GetSnapshot();

				snapshot1.Equals(snapshot1).Should().BeTrue();
				snapshot2.Equals(snapshot2).Should().BeTrue();
			}
		}
	}
}