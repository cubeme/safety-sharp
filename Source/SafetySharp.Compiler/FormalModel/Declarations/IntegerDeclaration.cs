namespace SafetySharp.Compiler.FormalModel.Declarations
{
	using System;

	public class IntegerDeclaration : DataTypeDeclaration
	{
		public int From { get; private set; }
		public int To { get; private set; }
		public OverflowBehavior OverflowBehavior { get; private set; }
	}
}