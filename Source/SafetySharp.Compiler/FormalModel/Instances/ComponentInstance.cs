namespace SafetySharp.Compiler.FormalModel.Instances
{
	using System;
	using System.Collections.Generic;
	using Declarations;

	public class ComponentInstance
	{
		public ComponentInstance(
			ComponentDeclaration declaration,
			List<ComponentInstance> subComponents,
			List<Literal> variables,
			List<PortBinding> bindings)
		{
			Declaration = declaration;
			SubComponents = subComponents;
			Variables = variables;
			Bindings = bindings;
		}

		public ComponentDeclaration Declaration { get; private set; }
		public List<Literal> Variables { get; private set; }
		public List<ComponentInstance> SubComponents { get; private set; }
		public List<PortBinding> Bindings { get; private set; }
	}
}