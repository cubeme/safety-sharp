namespace SafetySharp.Compiler.FormalModel.Declarations
{
	using System;

	public class ProvidedPartitionPortDeclaration
	{
		public string Name { get; private set; }
		public DataTypeDeclaration ReturnType { get; private set; }
		public ProvidedPortDeclaration Port { get; private set; }
	}
}