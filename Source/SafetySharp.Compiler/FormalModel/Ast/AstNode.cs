namespace SafetySharp.Compiler.FormalModel.Ast
{
	using System;

	public abstract class AstNode
	{
		public abstract void AcceptVisitor(IAstVisitor visitor);
	}
}