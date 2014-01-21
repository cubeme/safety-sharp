namespace SafetySharp.Compiler.FormalModel.Ast
{
	using System;
	using System.Collections.Generic;

	public class GuardedCommandStatement : Statement
	{
		public List<Expression> Conditions { get; private set; }
		public List<Statement> Statements { get; private set; }

		public override void AcceptVisitor(IAstVisitor visitor)
		{
			visitor.Visit(this);
		}
	}
}