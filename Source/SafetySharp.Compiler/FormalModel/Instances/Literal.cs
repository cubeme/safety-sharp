namespace SafetySharp.Compiler.FormalModel.Instances
{
	using System;
	using System.Linq;
	using Declarations;

	public struct Literal
	{
		public Literal(bool value)
			: this()
		{
			Value = value;
		}

		public Literal(int value)
			: this()
		{
			Value = value;
		}

		public Literal(decimal value)
			: this()
		{
			Value = value;
		}

		public Literal(params Literal[] values)
			: this()
		{
			Value = values;
		}

		public object Value { get; private set; }

		public Literal[] Values
		{
			get
			{
				Assert.That(IsTuple(), "The literal does not represent a value of tuple-type.");
				return Value as Literal[];
			}
		}

		public bool IsBoolean()
		{
			return Value is bool;
		}

		public bool IsInteger()
		{
			return Value is int;
		}

		public bool IsDecimal()
		{
			return Value is decimal;
		}

		public bool IsTuple()
		{
			return Value is Literal[];
		}

		public bool IsOfType(DataTypeDeclaration type)
		{
			Assert.ArgumentNotNull(type);

			if (IsBoolean())
				return type is BooleanDeclaration;

			if (IsInteger())
				return type is IntegerDeclaration;

			if (IsDecimal())
				return type is DecimalDeclaration;

			if (!IsTuple())
				return false;

			var tupleType = type as TupleDeclaration;
			if (tupleType == null)
				return false;

			var isOfType = true;

			if (Values.Length != tupleType.Elements.Length)
				return false;

			for (var i = 0; i < tupleType.Elements.Length; ++i)
				isOfType &= Values[i].IsOfType(tupleType.Elements[i]);

			return isOfType;
		}
	}
}