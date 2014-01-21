namespace SafetySharp.Compiler.FormalModel.Instances
{
	using System;
	using System.Collections.Generic;
	using Declarations;

	public class PartitionInstance
	{
		public PartitionDeclaration Declaration { get; private set; }
		public ComponentInstance Component { get; private set; }
		public List<Literal> ProvidedPorts { get; private set; }
		public List<PartitionPortBinding> Bindings { get; private set; }
	}
}