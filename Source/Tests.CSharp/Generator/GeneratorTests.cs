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
	using System.Linq;
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

		private static ImmutableArray<SimpleTestElement> CreateArray(params int[] values)
		{
			return values.Aggregate(ImmutableArray<SimpleTestElement>.Empty, (current, value) => current.Add(new SimpleTestElement(value)));
		}

		private static ImmutableList<SimpleTestElement> CreateList(params int[] values)
		{
			return values.Aggregate(ImmutableList<SimpleTestElement>.Empty, (current, value) => current.Add(new SimpleTestElement(value)));
		}

		private static ImmutableDictionary<string, SimpleTestElement> CreateDictionary(params Tuple<string, int>[] values)
		{
			return values.ToImmutableDictionary(value => value.Item1, value => new SimpleTestElement(value.Item2));
		}

		[Test]
		public void AddElementsToArray()
		{
			var element = new ArrayTestElement(CreateArray(1, 2, 3));
			element = element.AddArray(CreateArray(4, 5, 6).ToArray());

			element.Should().Be(new ArrayTestElement(CreateArray(1, 2, 3, 4, 5, 6)));
		}

		[Test]
		public void AddElementsToArray_ShouldThrowWhenNullIsPassed()
		{
			var element = new ArrayTestElement(CreateArray(1, 2, 3));
			Action action = () => element.AddArray(null);

			action.ShouldThrow<ArgumentNullException>();
		}

		[Test]
		public void AddElementsToDictionary()
		{
			var element = new DictionaryTestElement(CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2), Tuple.Create("C", 3)));
			element = element.AddDictionary(CreateDictionary(Tuple.Create("D", 4), Tuple.Create("E", 5), Tuple.Create("F", 6)));

			element.Should().Be(new DictionaryTestElement(CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2), Tuple.Create("C", 3),
																		   Tuple.Create("D", 4), Tuple.Create("E", 5), Tuple.Create("F", 6))));
		}

		[Test]
		public void AddElementsToDictionary_ShouldThrowWhenNullIsPassed()
		{
			var element = new DictionaryTestElement(CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2), Tuple.Create("C", 3)));
			Action action = () => element.AddDictionary(null);

			action.ShouldThrow<ArgumentNullException>();
		}

		[Test]
		public void AddElementsToList()
		{
			var element = new ListTestElement(CreateList(1, 2, 3));
			element = element.AddList(CreateList(4, 5, 6).ToArray());

			element.Should().Be(new ListTestElement(CreateList(1, 2, 3, 4, 5, 6)));
		}

		[Test]
		public void AddElementsToList_ShouldThrowWhenNullIsPassed()
		{
			var element = new ListTestElement(CreateList(1, 2, 3));
			Action action = () => element.AddList(null);

			action.ShouldThrow<ArgumentNullException>();
		}

		[Test]
		public void AddElementsToNullDictionary()
		{
			var element = new NullDictionaryTestElement(null);
			element = element.AddDictionary(CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2)));

			element.Should().Be(new NullDictionaryTestElement(CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2))));
		}

		[Test]
		public void AddElementsToNullList()
		{
			var element = new NullListTestElement(null);
			element = element.AddList(CreateList(1).ToArray());

			element.Should().Be(new NullListTestElement(CreateList(1)));
		}

		[Test]
		public void ArrayEquality()
		{
			var array1 = CreateArray(1, 2, 3);
			var array2 = CreateArray(1, 2, 3);

			var element1 = new ArrayTestElement(array1);
			var element2 = new ArrayTestElement(array2);
			(element1 == element2).Should().BeTrue();

			element2 = new ArrayTestElement(array1);
			(element1 == element2).Should().BeTrue();

			element1 = new ArrayTestElement(ImmutableArray<SimpleTestElement>.Empty);
			element2 = new ArrayTestElement(ImmutableArray<SimpleTestElement>.Empty);
			(element1 == element2).Should().BeTrue();
		}

		[Test]
		public void ArrayInequality()
		{
			var array1 = CreateArray(1, 2, 3);
			var array2 = CreateArray(1, 3);
			var array3 = CreateArray(1, 3, 2);

			var element1 = new ArrayTestElement(array1);
			var element2 = new ArrayTestElement(array2);
			(element1 == element2).Should().BeFalse();

			element2 = new ArrayTestElement(array3);
			(element1 == element2).Should().BeFalse();

			element2 = new ArrayTestElement(ImmutableArray<SimpleTestElement>.Empty);
			(element1 == element2).Should().BeFalse();
		}

		[Test]
		public void ArrayUpdateShouldReturnNewObject()
		{
			var element = new ArrayTestElement(CreateArray(1, 2, 3));
			var updatedElement = element.Update(CreateArray(4, 5, 6));

			ReferenceEquals(element, updatedElement).Should().BeFalse();
		}

		[Test]
		public void ArrayUpdateShouldReturnSameObject()
		{
			var element = new ArrayTestElement(CreateArray(1, 2, 3));
			var updatedElement = element.Update(CreateArray(1, 2, 3));

			ReferenceEquals(element, updatedElement).Should().BeTrue();
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
		public void DictionaryEquality()
		{
			var dictionary1 = CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2), Tuple.Create("C", 3));
			var dictionary2 = CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2), Tuple.Create("C", 3));

			var element1 = new DictionaryTestElement(dictionary1);
			var element2 = new DictionaryTestElement(dictionary2);
			(element1 == element2).Should().BeTrue();

			element2 = new DictionaryTestElement(dictionary1);
			(element1 == element2).Should().BeTrue();

			element1 = new DictionaryTestElement(ImmutableDictionary<string, SimpleTestElement>.Empty);
			element2 = new DictionaryTestElement(ImmutableDictionary<string, SimpleTestElement>.Empty);
			(element1 == element2).Should().BeTrue();

			// Order should not matter
			element1 = new DictionaryTestElement(CreateDictionary(Tuple.Create("B", 2), Tuple.Create("C", 3), Tuple.Create("A", 1)));
			element2 = new DictionaryTestElement(dictionary1);
			(element1 == element2).Should().BeTrue();
		}

		[Test]
		public void DictionaryInequality()
		{
			var dictionary1 = CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2), Tuple.Create("C", 3));
			var dictionary2 = CreateDictionary(Tuple.Create("A", 1), Tuple.Create("C", 3));
			var dictionary3 = CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2), Tuple.Create("D", 4));

			var element1 = new DictionaryTestElement(dictionary1);
			var element2 = new DictionaryTestElement(dictionary2);
			(element1 == element2).Should().BeFalse();

			element2 = new DictionaryTestElement(dictionary3);
			(element1 == element2).Should().BeFalse();

			element2 = new DictionaryTestElement(ImmutableDictionary<string, SimpleTestElement>.Empty);
			(element1 == element2).Should().BeFalse();
		}

		[Test]
		public void DictionaryUpdateShouldReturnNewObject()
		{
			var element = new DictionaryTestElement(CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2), Tuple.Create("C", 3)));
			var updatedElement = element.Update(CreateDictionary(Tuple.Create("D", 3)));

			ReferenceEquals(element, updatedElement).Should().BeFalse();
		}

		[Test]
		public void DictionaryUpdateShouldReturnSameObject()
		{
			var element = new DictionaryTestElement(CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2), Tuple.Create("C", 3)));
			var updatedElement = element.Update(CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2), Tuple.Create("C", 3)));

			ReferenceEquals(element, updatedElement).Should().BeTrue();
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
		public void ListEquality()
		{
			var list1 = CreateList(1, 2, 3);
			var list2 = CreateList(1, 2, 3);

			var element1 = new ListTestElement(list1);
			var element2 = new ListTestElement(list2);
			(element1 == element2).Should().BeTrue();

			element2 = new ListTestElement(list1);
			(element1 == element2).Should().BeTrue();

			element1 = new ListTestElement(ImmutableList<SimpleTestElement>.Empty);
			element2 = new ListTestElement(ImmutableList<SimpleTestElement>.Empty);
			(element1 == element2).Should().BeTrue();
		}

		[Test]
		public void ListInequality()
		{
			var list1 = CreateList(1, 2, 3);
			var list2 = CreateList(1, 3);
			var list3 = CreateList(1, 3, 2);

			var element1 = new ListTestElement(list1);
			var element2 = new ListTestElement(list2);
			(element1 == element2).Should().BeFalse();

			element2 = new ListTestElement(list3);
			(element1 == element2).Should().BeFalse();

			element2 = new ListTestElement(ImmutableList<SimpleTestElement>.Empty);
			(element1 == element2).Should().BeFalse();
		}

		[Test]
		public void ListUpdateShouldReturnNewObject()
		{
			var element = new ListTestElement(CreateList(1, 2, 3));
			var updatedElement = element.Update(CreateList(4, 5, 6));

			ReferenceEquals(element, updatedElement).Should().BeFalse();
		}

		[Test]
		public void ListUpdateShouldReturnSameObject()
		{
			var element = new ListTestElement(CreateList(1, 2, 3));
			var updatedElement = element.Update(CreateList(1, 2, 3));

			ReferenceEquals(element, updatedElement).Should().BeTrue();
		}

		[Test]
		public void NullDictionaryEquality()
		{
			var dictionary1 = CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2), Tuple.Create("C", 3));
			var dictionary2 = CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2), Tuple.Create("C", 3));

			var element1 = new NullDictionaryTestElement(dictionary1);
			var element2 = new NullDictionaryTestElement(dictionary2);
			(element1 == element2).Should().BeTrue();

			element2 = new NullDictionaryTestElement(dictionary1);
			(element1 == element2).Should().BeTrue();

			element1 = new NullDictionaryTestElement(ImmutableDictionary<string, SimpleTestElement>.Empty);
			element2 = new NullDictionaryTestElement(ImmutableDictionary<string, SimpleTestElement>.Empty);
			(element1 == element2).Should().BeTrue();

			element1 = new NullDictionaryTestElement(null);
			element2 = new NullDictionaryTestElement(null);
			(element1 == element2).Should().BeTrue();
		}

		[Test]
		public void NullDictionaryUpdateShouldReturnNewObject()
		{
			var element = new NullDictionaryTestElement(null);
			var updatedElement = element.Update(CreateDictionary(Tuple.Create("D", 3)));

			ReferenceEquals(element, updatedElement).Should().BeFalse();

			element = new NullDictionaryTestElement(CreateDictionary(Tuple.Create("D", 3)));
			updatedElement = element.Update(null);

			ReferenceEquals(element, updatedElement).Should().BeFalse();
		}

		[Test]
		public void NullDictionaryUpdateShouldReturnSameObject()
		{
			var element = new NullDictionaryTestElement(null);
			var updatedElement = element.Update(null);

			ReferenceEquals(element, updatedElement).Should().BeTrue();
		}

		[Test]
		public void NullDictionarytInequality()
		{
			var dictionary1 = CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2), Tuple.Create("C", 3));
			var dictionary2 = CreateDictionary(Tuple.Create("A", 1), Tuple.Create("C", 3));
			var dictionary3 = CreateDictionary(Tuple.Create("A", 1), Tuple.Create("B", 2), Tuple.Create("D", 4));

			var element1 = new NullDictionaryTestElement(dictionary1);
			var element2 = new NullDictionaryTestElement(dictionary2);
			(element1 == element2).Should().BeFalse();

			element2 = new NullDictionaryTestElement(dictionary3);
			(element1 == element2).Should().BeFalse();

			element2 = new NullDictionaryTestElement(ImmutableDictionary<string, SimpleTestElement>.Empty);
			(element1 == element2).Should().BeFalse();

			element1 = new NullDictionaryTestElement(null);
			(element1 == element2).Should().BeFalse();

			element1 = new NullDictionaryTestElement(dictionary1);
			element2 = new NullDictionaryTestElement(null);
			(element1 == element2).Should().BeFalse();
		}

		[Test]
		public void NullListEquality()
		{
			var list1 = CreateList(1, 2, 3);
			var list2 = CreateList(1, 2, 3);

			var element1 = new NullListTestElement(list1);
			var element2 = new NullListTestElement(list2);
			(element1 == element2).Should().BeTrue();

			element2 = new NullListTestElement(list1);
			(element1 == element2).Should().BeTrue();

			element1 = new NullListTestElement(ImmutableList<SimpleTestElement>.Empty);
			element2 = new NullListTestElement(ImmutableList<SimpleTestElement>.Empty);
			(element1 == element2).Should().BeTrue();

			element1 = new NullListTestElement(null);
			element2 = new NullListTestElement(null);
			(element1 == element2).Should().BeTrue();
		}

		[Test]
		public void NullListInequality()
		{
			var list1 = CreateList(1, 2, 3);
			var list2 = CreateList(1, 3);
			var list3 = CreateList(1, 3, 2);

			var element1 = new NullListTestElement(list1);
			var element2 = new NullListTestElement(list2);
			(element1 == element2).Should().BeFalse();

			element2 = new NullListTestElement(list3);
			(element1 == element2).Should().BeFalse();

			element2 = new NullListTestElement(ImmutableList<SimpleTestElement>.Empty);
			(element1 == element2).Should().BeFalse();

			element1 = new NullListTestElement(null);
			(element1 == element2).Should().BeFalse();

			element1 = new NullListTestElement(list1);
			element2 = new NullListTestElement(null);
			(element1 == element2).Should().BeFalse();
		}

		[Test]
		public void NullListUpdateShouldReturnNewObject()
		{
			var element = new NullListTestElement(null);
			var updatedElement = element.Update(CreateList(4, 5, 6));

			ReferenceEquals(element, updatedElement).Should().BeFalse();

			element = new NullListTestElement(CreateList(1, 2, 3));
			updatedElement = element.Update(null);

			ReferenceEquals(element, updatedElement).Should().BeFalse();
		}

		[Test]
		public void NullListUpdateShouldReturnSameObject()
		{
			var element = new NullListTestElement(null);
			var updatedElement = element.Update(null);

			ReferenceEquals(element, updatedElement).Should().BeTrue();
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
		public void UpdateShouldReturnNewObject()
		{
			var element = new SimpleTestElement(1);
			var updatedElement = element.Update(2);

			ReferenceEquals(element, updatedElement).Should().BeFalse();
		}

		[Test]
		public void UpdateShouldReturnSameObject()
		{
			var element = new SimpleTestElement(1);
			var updatedElement = element.Update(1);

			ReferenceEquals(element, updatedElement).Should().BeTrue();
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
	}
}