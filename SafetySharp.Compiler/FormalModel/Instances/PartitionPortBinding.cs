namespace SafetySharp.Compiler.FormalModel.Instances
{
	using System;
	using Declarations;

	public class PartitionPortBinding
	{
		public PartitionInstance Partition { get; private set; }
		public ProvidedPartitionPortDeclaration Port { get; private set; }
	}
}