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

namespace Tests.Generator
{
	using System;
	using System.Collections.Immutable;
	using FluentAssertions;
	using NUnit.Framework;

	[TestFixture]
	internal class GeneratorTests
	{
		private static void ObjectsShouldBeEqual(object nullObject)
		{
			var notNullObject = new object();
			var notEmptyString = "Test";

			var element1 = new ValidationTestElement(nullObject, notNullObject, notEmptyString);
			var element2 = new ValidationTestElement(nullObject, notNullObject, notEmptyString);

			(element1 == element2).Should().BeTrue();
			(element1 != element2).Should().BeFalse();
			(element1.Equals(element2)).Should().BeTrue();
			(element1.Equals((object)element2)).Should().BeTrue();
			(element1.Equals((object)null)).Should().BeFalse();
		}

		[Test]
		public void ObjectsShouldNotBeEqual()
		{
			var nullObject = new object();
			var notNullObject = new object();
			var notEmptyString = "Test";

			var element1 = new ValidationTestElement(nullObject, notNullObject, notEmptyString);
			var element2 = new ValidationTestElement(null, notNullObject, notEmptyString);

			(element1 == element2).Should().BeFalse();
			(element1 != element2).Should().BeTrue();
			(element1.Equals(element2)).Should().BeFalse();
			(element1.Equals((object)element2)).Should().BeFalse();

			element1 = new ValidationTestElement(nullObject, notNullObject, notEmptyString);
			element2 = new ValidationTestElement(nullObject, notNullObject, notEmptyString + "X");

			(element1 == element2).Should().BeFalse();
			(element1 != element2).Should().BeTrue();
			(element1.Equals(element2)).Should().BeFalse();
			(element1.Equals((object)element2)).Should().BeFalse();
		}

		[Test]
		public void GetHashCodeShouldNeverThrow()
		{
			var nullObject = new object();
			var notNullObject = new object();
			var notEmptyString = "Test";
			var value = 1;

			TestElement element = null;
			Action getHashCode = () => element.GetHashCode();

			element = new ValidationTestElement(nullObject, notNullObject, notEmptyString);
			getHashCode.ShouldNotThrow();

			element = new ValidationTestElement(null, notNullObject, notEmptyString);
			getHashCode.ShouldNotThrow();

			element = new InheritedValidationTestElement(nullObject, notNullObject, notEmptyString, value);
			getHashCode.ShouldNotThrow();

			element = new InheritedValidationTestElement(null, notNullObject, notEmptyString, value);
			getHashCode.ShouldNotThrow();
		}

		[Test]
		public void BaseObjectsShouldNotBeEqual()
		{
			var nullObject = new object();
			var notNullObject = new object();
			var notEmptyString = "Test";
			var value = 1;

			var element1 = new InheritedValidationTestElement(nullObject, notNullObject, notEmptyString, value);
			var element2 = new InheritedValidationTestElement(null, notNullObject, notEmptyString, value);

			(element1 == element2).Should().BeFalse();
			(element1 != element2).Should().BeTrue();
			(element1.Equals(element2)).Should().BeFalse();
			(element1.Equals((object)element2)).Should().BeFalse();

			element1 = new InheritedValidationTestElement(nullObject, notNullObject, notEmptyString, value);
			element2 = new InheritedValidationTestElement(nullObject, notNullObject, notEmptyString + "X", value);

			(element1 == element2).Should().BeFalse();
			(element1 != element2).Should().BeTrue();
			(element1.Equals(element2)).Should().BeFalse();
			(element1.Equals((object)element2)).Should().BeFalse();

			element1 = new InheritedValidationTestElement(nullObject, notNullObject, notEmptyString, value);
			element2 = new InheritedValidationTestElement(nullObject, notNullObject, notEmptyString, value + 17);

			(element1 == element2).Should().BeFalse();
			(element1 != element2).Should().BeTrue();
			(element1.Equals(element2)).Should().BeFalse();
			(element1.Equals((object)element2)).Should().BeFalse();
		}

		private static void BaseObjectsShouldBeEqual(object nullObject)
		{
			var notNullObject = new object();
			var notEmptyString = "Test";

			var element1 = new InheritedValidationTestElement(nullObject, notNullObject, notEmptyString, 3);
			var element2 = new InheritedValidationTestElement(nullObject, notNullObject, notEmptyString, 3);

			(element1 == element2).Should().BeTrue();
			(element1 != element2).Should().BeFalse();
			(element1.Equals(element2)).Should().BeTrue();
			(element1.Equals((object)element2)).Should().BeTrue();
			(element1.Equals((object)null)).Should().BeFalse();
		}

		[Test]
		public void BasePropertiesShouldBeSet()
		{
			var nullObject = new object();
			var notNullObject = new object();
			var notEmptyString = "Test";
			var value = 17;

			var element = new InheritedValidationTestElement(nullObject, notNullObject, notEmptyString, value);
			element.NullObject.Should().Be(nullObject);
			element.NotNullObject.Should().Be(notNullObject);
			element.NotEmpty.Should().Be(notEmptyString);
			element.Value.Should().Be(value);

			value = 33;
			element = element.WithNullObject(null).WithValue(value);
			element.NullObject.Should().Be(null);
			element.NotNullObject.Should().Be(notNullObject);
			element.NotEmpty.Should().Be(notEmptyString);
			element.Value.Should().Be(value);
		}

		[Test]
		public void BaseValidationShouldFail()
		{
			Action action = () => new InheritedValidationTestElement(new object(), null, "Test", 1);
			action.ShouldThrow<Exception>();

			action = () => new InheritedValidationTestElement(new object(), new object(), null, 1);
			action.ShouldThrow<Exception>();

			action = () => new InheritedValidationTestElement(new object(), new object(), " \t\r ", 1);
			action.ShouldThrow<Exception>();

			var element = new InheritedValidationTestElement(new object(), new object(), "Test", 3);
			action = () => element.WithNotEmpty("");
			action.ShouldThrow<Exception>();
		}

		[Test]
		public void BaseValidationShouldSucceed()
		{
			Action action = () => new InheritedValidationTestElement(new object(), new object(), "Test", 1);
			action.ShouldNotThrow();

			action = () => new InheritedValidationTestElement(null, new object(), "Test", 1);
			action.ShouldNotThrow();
		}

		[Test]
		public void ObjectsShouldBeEqualNotNull()
		{
			ObjectsShouldBeEqual(new object());
		}

		[Test]
		public void ObjectsShouldBeEqualNull()
		{
			ObjectsShouldBeEqual(null);
		}

		[Test]
		public void BaseObjectsShouldBeEqualNotNull()
		{
			BaseObjectsShouldBeEqual(new object());
		}

		[Test]
		public void BaseObjectsShouldBeEqualNull()
		{
			BaseObjectsShouldBeEqual(null);
		}

		[Test]
		public void PropertiesShouldBeSet()
		{
			var nullObject = new object();
			var notNullObject = new object();
			var notEmptyString = "Test";

			var element = new ValidationTestElement(nullObject, notNullObject, notEmptyString);
			element.NullObject.Should().Be(nullObject);
			element.NotNullObject.Should().Be(notNullObject);
			element.NotEmpty.Should().Be(notEmptyString);

			element = element.WithNullObject(null);
			element.NullObject.Should().Be(null);
			element.NotNullObject.Should().Be(notNullObject);
			element.NotEmpty.Should().Be(notEmptyString);
		}

		[Test]
		public void ValidationShouldFail()
		{
			Action action = () => new ValidationTestElement(new object(), null, "Test");
			action.ShouldThrow<Exception>();

			action = () => new ValidationTestElement(new object(), new object(), null);
			action.ShouldThrow<Exception>();

			action = () => new ValidationTestElement(new object(), new object(), "");
			action.ShouldThrow<Exception>();

			action = () => new ValidationTestElement(new object(), new object(), " \n ");
			action.ShouldThrow<Exception>();

			var element = new ValidationTestElement(new object(), new object(), "Test");
			action = () => element.WithNotEmpty("");
			action.ShouldThrow<Exception>();
		}

		[Test]
		public void ValidationShouldSucceed()
		{
			Action action = () => new ValidationTestElement(new object(), new object(), "Test");
			action.ShouldNotThrow();

			action = () => new ValidationTestElement(null, new object(), "Test");
			action.ShouldNotThrow();
		}

		[Test]
		public void ArrayEquality()
		{
			var array1 = ImmutableArray.Create(1, 2, 3);
			var array2 = ImmutableArray.Create(1, 2, 3);

			var element1 = new ArrayTestElement(array1);
			var element2 = new ArrayTestElement(array2);
			(element1 == element2).Should().BeTrue();

			element2 = new ArrayTestElement(array1);
			(element1 == element2).Should().BeTrue();

			element1 = new ArrayTestElement(ImmutableArray<int>.Empty);
			element2 = new ArrayTestElement(ImmutableArray<int>.Empty);
			(element1 == element2).Should().BeTrue();
		}

		[Test]
		public void ArrayInequality()
		{
			var array1 = ImmutableArray.Create(1, 2, 3);
			var array2 = ImmutableArray.Create(1, 3);
			var array3 = ImmutableArray.Create(1, 3, 2);

			var element1 = new ArrayTestElement(array1);
			var element2 = new ArrayTestElement(array2);
			(element1 == element2).Should().BeFalse();

			element2 = new ArrayTestElement(array3);
			(element1 == element2).Should().BeFalse();

			element2 = new ArrayTestElement(ImmutableArray<int>.Empty);
			(element1 == element2).Should().BeFalse();
		}

		[Test]
		public void ListEquality()
		{
			var list1 = ImmutableList.Create(1, 2, 3);
			var list2 = ImmutableList.Create(1, 2, 3);

			var element1 = new ListTestElement(list1);
			var element2 = new ListTestElement(list2);
			(element1 == element2).Should().BeTrue();

			element2 = new ListTestElement(list1);
			(element1 == element2).Should().BeTrue();

			element1 = new ListTestElement(ImmutableList<int>.Empty);
			element2 = new ListTestElement(ImmutableList<int>.Empty);
			(element1 == element2).Should().BeTrue();
		}

		[Test]
		public void ListInequality()
		{
			var list1 = ImmutableList.Create(1, 2, 3);
			var list2 = ImmutableList.Create(1, 3);
			var list3 = ImmutableList.Create(1, 3, 2);

			var element1 = new ListTestElement(list1);
			var element2 = new ListTestElement(list2);
			(element1 == element2).Should().BeFalse();

			element2 = new ListTestElement(list3);
			(element1 == element2).Should().BeFalse();

			element2 = new ListTestElement(ImmutableList<int>.Empty);
			(element1 == element2).Should().BeFalse();
		}

		[Test]
		public void NullListEquality()
		{
			var list1 = ImmutableList.Create(1, 2, 3);
			var list2 = ImmutableList.Create(1, 2, 3);

			var element1 = new NullListTestElement(list1);
			var element2 = new NullListTestElement(list2);
			(element1 == element2).Should().BeTrue();

			element2 = new NullListTestElement(list1);
			(element1 == element2).Should().BeTrue();

			element1 = new NullListTestElement(ImmutableList<int>.Empty);
			element2 = new NullListTestElement(ImmutableList<int>.Empty);
			(element1 == element2).Should().BeTrue();

			element1 = new NullListTestElement(null);
			element2 = new NullListTestElement(null);
			(element1 == element2).Should().BeTrue();
		}

		[Test]
		public void NullListInequality()
		{
			var list1 = ImmutableList.Create(1, 2, 3);
			var list2 = ImmutableList.Create(1, 3);
			var list3 = ImmutableList.Create(1, 3, 2);

			var element1 = new NullListTestElement(list1);
			var element2 = new NullListTestElement(list2);
			(element1 == element2).Should().BeFalse();

			element2 = new NullListTestElement(list3);
			(element1 == element2).Should().BeFalse();

			element2 = new NullListTestElement(ImmutableList<int>.Empty);
			(element1 == element2).Should().BeFalse();

			element1 = new NullListTestElement(null);
			(element1 == element2).Should().BeFalse();

			element1 = new NullListTestElement(list1);
			element2 = new NullListTestElement(null);
			(element1 == element2).Should().BeFalse();
		}
	}
}