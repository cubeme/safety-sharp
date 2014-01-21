namespace SafetySharp.Compiler.FormalModel.Ast
{
	using System;
	using Instances;

	public class LiteralExpression : Expression
	{
		public Literal Literal { get; private set; }

		public override void AcceptVisitor(IAstVisitor visitor)
		{
			visitor.Visit(this);
		}
	}
}