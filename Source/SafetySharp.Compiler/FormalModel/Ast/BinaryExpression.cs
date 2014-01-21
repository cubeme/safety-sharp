namespace SafetySharp.Compiler.FormalModel.Ast
{
	using System;

	public class BinaryExpression : Expression
	{
		public BinaryOperator Operator { get; private set; }
		public Expression LeftExpression { get; private set; }
		public Expression RightExpression { get; private set; }

		public override void AcceptVisitor(IAstVisitor visitor)
		{
			visitor.Visit(this);
		}
	}
}