namespace SafetySharp.Compiler.FormalModel.Ast
{
	using System;

	public interface IAstVisitor
	{
		void Visit(AssignmentStatement statement);
		void Visit(GuardedCommandStatement statement);
		void Visit(ReadPortStatement statement);
		void Visit(ReturnStatement statement);

		void Visit(ReadPartitionPortExpression expression);
		void Visit(UnaryExpression expression);
		void Visit(BinaryExpression expression);
		void Visit(VariableExpression expression);
		void Visit(LiteralExpression expression);
	}
}