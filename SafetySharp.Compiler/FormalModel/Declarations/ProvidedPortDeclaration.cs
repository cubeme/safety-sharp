namespace SafetySharp.Compiler.FormalModel.Declarations
{
	using System;
	using System.Collections.Generic;
	using Ast;

	public class ProvidedPortDeclaration
	{
		public string Name { get; private set; }
		public DataTypeDeclaration ReturnType { get; private set; }
		public List<DataTypeDeclaration> ParameterTypes { get; private set; }
		public Statement Statement { get; private set; }
	}
}