namespace SafetySharp.Compiler.FormalModel.Ast
{
	using System;
	using Declarations;

	public class ReadPartitionPortExpression : Expression
	{
		public RequiredPartitionPortDeclaration Port { get; private set; }

		public override void AcceptVisitor(IAstVisitor visitor)
		{
			visitor.Visit(this);
		}
	}
}