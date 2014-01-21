namespace SafetySharp.Compiler.FormalModel.Declarations
{
	using System;
	using System.Collections.Generic;

	public class RequiredPortDeclaration
	{
		public string Name { get; private set; }
		public DataTypeDeclaration ReturnType { get; private set; }
		public List<DataTypeDeclaration> ParameterTypes { get; private set; }
		public int Slot { get; private set; }
	}
}