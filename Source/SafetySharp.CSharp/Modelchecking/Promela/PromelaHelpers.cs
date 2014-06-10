using System;

namespace SafetySharp.Modelchecking.Promela
{
    using System.Collections.Immutable;
    using Expressions;
    using Statements;

    internal static class PromelaHelpers
    {
        public static Expressions.BooleanLiteral ConstTrueExpression()
        {
            return new Expressions.BooleanLiteral(true);
        }

        public static Expressions.BooleanLiteral ConstFalseExpression()
        {
            return new Expressions.BooleanLiteral(false);
        }

        public static Statement CoverStatementInEndlessLoop(Statement statement)
        {
            var trueGuard = new Expressions.BooleanLiteral(true);
            var clause = new Statements.GuardedCommandExpressionClause(trueGuard, statement);
            return new Statements.GuardedCommandRepetitionStatement(
                ImmutableArray<Statements.GuardedCommandClause>.Empty.Add(clause));
        }

        public static Statement SimpleFieldAssignment(string fieldName, Expression expr)
        {
            return new Statements.AssignmentStatement(new Expressions.VariableReferenceExpression(fieldName, null, null), expr);
        }
    }
}