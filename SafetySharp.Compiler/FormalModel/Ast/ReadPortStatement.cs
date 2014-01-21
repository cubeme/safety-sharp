namespace SafetySharp.Compiler.FormalModel.Ast
{
	using System;
	using Declarations;

	public class ReadPortStatement : Statement
	{
		public RequiredPortDeclaration Port { get; private set; }
		public VariableDeclaration Variable { get; private set; }

		public override void AcceptVisitor(IAstVisitor visitor)
		{
			visitor.Visit(this);
		}
	}
}