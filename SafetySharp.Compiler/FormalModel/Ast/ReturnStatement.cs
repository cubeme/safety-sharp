namespace SafetySharp.Compiler.FormalModel.Ast
{
	using System;

	public class ReturnStatement : Statement
	{
		public Expression Expression { get; private set; }

		public override void AcceptVisitor(IAstVisitor visitor)
		{
			visitor.Visit(this);
		}
	}
}