namespace SafetySharp.Compiler.FormalModel.Declarations
{
	using System;

	public class TupleDeclaration : DataTypeDeclaration
	{
		public TupleDeclaration(params DataTypeDeclaration[] elements)
		{
			Elements = elements;
		}

		public DataTypeDeclaration[] Elements { get; private set; }
	}
}