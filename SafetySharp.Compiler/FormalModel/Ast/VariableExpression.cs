namespace SafetySharp.Compiler.FormalModel.Ast
{
	using System;
	using Declarations;

	public class VariableExpression : Expression
	{
		public VariableDeclaration Variable { get; private set; }

		public override void AcceptVisitor(IAstVisitor visitor)
		{
			visitor.Visit(this);
		}
	}
}