namespace SafetySharp.Compiler.FormalModel.Declarations
{
	using System;

	public class RequiredPartitionPortDeclaration
	{
		public string Name { get; private set; }
		public DataTypeDeclaration ReturnType { get; private set; }
		public int Slot { get; private set; }
	}
}