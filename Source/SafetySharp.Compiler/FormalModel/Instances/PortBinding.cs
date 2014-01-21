namespace SafetySharp.Compiler.FormalModel.Instances
{
	using System;
	using Declarations;

	public class PortBinding
	{
		public ComponentInstance Component { get; private set; }
		public ProvidedPortDeclaration Port { get; private set; }
	}
}