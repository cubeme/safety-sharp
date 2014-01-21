namespace SafetySharp.Compiler.FormalModel.Declarations
{
	using System;
	using System.Collections.Generic;

	public class PartitionDeclaration
	{
		public string Name;
		public List<ProvidedPartitionPortDeclaration> ProvidedPorts { get; private set; }
		public List<RequiredPartitionPortDeclaration> RequiredPorts { get; private set; }
		public ComponentDeclaration Component { get; private set; }
	}
}