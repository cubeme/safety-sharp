namespace SafetySharp.Compiler.FormalModel.Declarations
{
	using System;

	public class VariableDeclaration
	{
		public string Name { get; private set; }
		public int Slot { get; private set; }
		public DataTypeDeclaration Type { get; private set; }
	}
}