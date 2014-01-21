namespace SafetySharp.Compiler.FormalModel.Declarations
{
	using System;
	using System.Collections.Generic;
	using System.Diagnostics.Contracts;
	using Instances;
	using Ast;

	public class ComponentDeclaration
	{
		public string Name { get; private set; }
		public List<ProvidedPortDeclaration> ProvidedPorts { get; private set; }
		public List<RequiredPortDeclaration> RequiredPorts { get; private set; }
		public List<ComponentDeclaration> SubComponents { get; private set; }
		public List<VariableDeclaration> Variables { get; private set; }
		public Statement UpdateStatement { get; private set; }

		public ComponentInstance Instantiate(
			List<ComponentInstance> subComponents,
			List<Literal> initialValues,
			List<PortBinding> bindings)
		{
			Contract.Requires(subComponents != null);
			Contract.Requires(subComponents.Count == SubComponents.Count);
			Contract.ForAll(0, initialValues.Count, i => initialValues[i].IsOfType(Variables[i].Type));

			return new ComponentInstance(this, subComponents, initialValues, bindings);
		}
	}
}