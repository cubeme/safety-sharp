namespace Tests
{
	using System;
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.Compiler.FormalModel.Declarations;
	using SafetySharp.Compiler.FormalModel.Instances;

	[TestFixture]
	public class LiteralTests
	{
		private readonly BooleanDeclaration _booleanDeclaration = new BooleanDeclaration();
		private readonly IntegerDeclaration _integerDeclaration = new IntegerDeclaration();
		private readonly DecimalDeclaration _decimalDeclaration = new DecimalDeclaration();
		private readonly TupleDeclaration _tupleDeclaration = new TupleDeclaration();

		[Test]
		public void CreateBoolean()
		{
			const bool value = true;
			var literal = new Literal(value);

			literal.Value.Should().BeOfType<bool>();
			literal.Value.Should().Be(value);
			literal.IsBoolean().Should().BeTrue();
			literal.IsInteger().Should().BeFalse();
			literal.IsDecimal().Should().BeFalse();
			literal.IsTuple().Should().BeFalse();
		}

		[Test]
		public void CreateDecimal()
		{
			const decimal value = 3.14m;
			var literal = new Literal(value);

			literal.Value.Should().BeOfType<decimal>();
			literal.Value.Should().Be(value);
			literal.IsBoolean().Should().BeFalse();
			literal.IsInteger().Should().BeFalse();
			literal.IsDecimal().Should().BeTrue();
			literal.IsTuple().Should().BeFalse();
		}

		[Test]
		public void CreateInteger()
		{
			const int value = 2;
			var literal = new Literal(value);

			literal.Value.Should().BeOfType<int>();
			literal.Value.Should().Be(value);
			literal.IsBoolean().Should().BeFalse();
			literal.IsInteger().Should().BeTrue();
			literal.IsDecimal().Should().BeFalse();
			literal.IsTuple().Should().BeFalse();
		}

		[Test]
		public void CreateTuple()
		{
			var value = new[] { new Literal(1), new Literal(2) };
			var literal = new Literal(value);

			literal.Value.Should().BeOfType<Literal[]>();
			literal.Value.Should().Be(value);
			literal.Values.Should().ContainInOrder(value);
			literal.IsBoolean().Should().BeFalse();
			literal.IsInteger().Should().BeFalse();
			literal.IsDecimal().Should().BeFalse();
			literal.IsTuple().Should().BeTrue();
		}

		[Test]
		public void IsOfTypeBoolean()
		{
			var literal = new Literal(true);

			literal.IsOfType(_booleanDeclaration).Should().BeTrue();
			literal.IsOfType(_integerDeclaration).Should().BeFalse();
			literal.IsOfType(_decimalDeclaration).Should().BeFalse();
			literal.IsOfType(_tupleDeclaration).Should().BeFalse();
		}

		[Test]
		public void IsOfTypeDecimal()
		{
			var literal = new Literal(3.14m);

			literal.IsOfType(_booleanDeclaration).Should().BeFalse();
			literal.IsOfType(_integerDeclaration).Should().BeFalse();
			literal.IsOfType(_decimalDeclaration).Should().BeTrue();
			literal.IsOfType(_tupleDeclaration).Should().BeFalse();
		}

		[Test]
		public void IsOfTypeInteger()
		{
			var literal = new Literal(2);

			literal.IsOfType(_booleanDeclaration).Should().BeFalse();
			literal.IsOfType(_integerDeclaration).Should().BeTrue();
			literal.IsOfType(_decimalDeclaration).Should().BeFalse();
			literal.IsOfType(_tupleDeclaration).Should().BeFalse();
		}

		[Test]
		public void IsOfTypeTuple()
		{
			var literal = new Literal(new[] { new Literal(1), new Literal(2) });
			var tupleDeclaration = new TupleDeclaration(new IntegerDeclaration(), new IntegerDeclaration());

			literal.IsOfType(_booleanDeclaration).Should().BeFalse();
			literal.IsOfType(_integerDeclaration).Should().BeFalse();
			literal.IsOfType(_decimalDeclaration).Should().BeFalse();
			literal.IsOfType(tupleDeclaration).Should().BeTrue();
		}

		[Test]
		public void IsOfOtherTupleTypeFirstElement()
		{
			var literal = new Literal(new[] { new Literal(1), new Literal(2) });
			var tupleDeclaration = new TupleDeclaration(new DecimalDeclaration(), new IntegerDeclaration());

			literal.IsOfType(tupleDeclaration).Should().BeFalse();
		}

		[Test]
		public void IsOfOtherTupleTypeSecondElement()
		{
			var literal = new Literal(new[] { new Literal(1), new Literal(2) });
			var tupleDeclaration = new TupleDeclaration(new IntegerDeclaration(), new DecimalDeclaration());

			literal.IsOfType(tupleDeclaration).Should().BeFalse();
		}

		[Test]
		public void IsOfOtherTupleTypeOtherElementCount()
		{
			var literal = new Literal(new[] { new Literal(1), new Literal(2) });
			var tupleDeclaration = new TupleDeclaration(new IntegerDeclaration(), new BooleanDeclaration(), new DecimalDeclaration());

			literal.IsOfType(tupleDeclaration).Should().BeFalse();
		}

		[Test]
		public void CreateNestedTuple()
		{
			var inner = new Literal(new Literal(false), new Literal(2.0m));
			var center = new Literal(inner, new Literal(1));

			var value = new[] { new Literal(1), center, new Literal(2) };
			var outer = new Literal(value);

			outer.Value.Should().BeOfType<Literal[]>();
			outer.Values.Should().ContainInOrder(value);
			outer.IsBoolean().Should().BeFalse();
			outer.IsInteger().Should().BeFalse();
			outer.IsDecimal().Should().BeFalse();
			outer.IsTuple().Should().BeTrue();
		}

		[Test]
		public void IsOfTypeNestedTuple()
		{
			var inner = new Literal(new Literal(false), new Literal(2.0m));
			var center = new Literal( inner, new Literal(1) );
			var outer = new Literal( new Literal(1), center, new Literal(2) );

			var innerType = new TupleDeclaration(new BooleanDeclaration(), new DecimalDeclaration());
			var centerType = new TupleDeclaration(innerType, new IntegerDeclaration());
			var tupleDeclaration = new TupleDeclaration(new IntegerDeclaration(), centerType, new IntegerDeclaration());

			outer.IsOfType(_booleanDeclaration).Should().BeFalse();
			outer.IsOfType(_integerDeclaration).Should().BeFalse();
			outer.IsOfType(_decimalDeclaration).Should().BeFalse();
			outer.IsOfType(tupleDeclaration).Should().BeTrue();
		}
	}
}