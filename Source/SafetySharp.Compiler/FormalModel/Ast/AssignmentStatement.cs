namespace SafetySharp.Compiler.FormalModel.Ast
{
	using System;
	using Declarations;

	public class AssignmentStatement : Statement
	{
		public VariableDeclaration Variable { get; private set; }
		public Expression Expression { get; private set; }

		public override void AcceptVisitor(IAstVisitor visitor)
		{
			visitor.Visit(this);
		}
	}
}