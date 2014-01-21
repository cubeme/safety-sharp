namespace SafetySharp.Compiler.FormalModel.Declarations
{
	using System;

	public class DecimalDeclaration : DataTypeDeclaration
	{
		public decimal From { get; private set; }
		public decimal To { get; private set; }
		public OverflowBehavior OverflowBehavior { get; private set; }
	}
}