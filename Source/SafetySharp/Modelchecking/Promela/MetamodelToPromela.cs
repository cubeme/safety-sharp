// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

namespace SafetySharp.Modelchecking.Promela
{
    using System;
    using System.Collections.Generic;
    using System.Collections.Immutable;
    using System.Linq;
    using Metamodel;
    using Utilities;
    using MMExpressions = Metamodel.Expressions;
    using MMStatements = Metamodel.Statements;
    using PrExpression = Expressions.Expression;
    using PrStatement = Statements.Statement;
    using PrExpressions = Expressions;
    using PrStatements = Statements;

    #region Expressions

    internal class MetamodelToPromela
    {
        public MetamodelToPromela()
        {
            ExpressionVisitor = new MetamodelExpressionToPromelaExpression(this);
            StatementVisitor = new MetamodelStatementToPromelaStatement(this);

        }
        public MetamodelExpressionToPromelaExpression ExpressionVisitor { get; private set; }
        public MetamodelStatementToPromelaStatement StatementVisitor { get; private set; }

        readonly object _objectToUniqueNameLocker = new object();

        private int _objectToUniqueNameIterator = 0;

        private readonly Dictionary<object,string> _objectToUniqueName = new Dictionary<object, string>();

        public string GetUniqueName(object input)
        {
            lock (_objectToUniqueNameLocker)
            {
                string value;
                if (_objectToUniqueName.TryGetValue(input, out value))
                    return value;
                _objectToUniqueNameIterator++;
                value = "variable_" + _objectToUniqueNameIterator.ToString();
                _objectToUniqueName.Add(input,value);
                return value;
            }
        }
    }

    internal class MetamodelExpressionToPromelaExpression : MetamodelVisitor<PrExpression>
    {
        private MetamodelToPromela CommonKnowledge { get; set; }
        public MetamodelExpressionToPromelaExpression(MetamodelToPromela commonKnowledge)
        {
            CommonKnowledge = commonKnowledge;
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMExpressions.BooleanLiteral" />.
        /// </summary>
        /// <param name="booleanLiteral">The <see cref="MMExpressions.BooleanLiteral" /> instance that should be visited.</param>
        public override PrExpression VisitBooleanLiteral(MMExpressions.BooleanLiteral booleanLiteral)
        {
            Argument.NotNull(booleanLiteral, () => booleanLiteral);
            return new PrExpressions.BooleanLiteral(booleanLiteral.Value);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMExpressions.IntegerLiteral" />.
        /// </summary>
        /// <param name="integerLiteral">The <see cref="MMExpressions.IntegerLiteral" /> instance that should be visited.</param>
        public override PrExpression VisitIntegerLiteral(MMExpressions.IntegerLiteral integerLiteral)
        {
            Argument.NotNull(integerLiteral, () => integerLiteral);
            return new PrExpressions.NumberLiteral(integerLiteral.Value);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMExpressions.DecimalLiteral" />.
        /// </summary>
        /// <param name="decimalLiteral">The <see cref="MMExpressions.DecimalLiteral" /> instance that should be visited.</param>
        public override PrExpression VisitDecimalLiteral(MMExpressions.DecimalLiteral decimalLiteral)
        {
            Argument.NotNull(decimalLiteral, () => decimalLiteral);
            throw new NotImplementedException();
        }

        private PromelaBinaryOperator MmBinOperatorToPrBinOperator(MMExpressions.BinaryOperator @operator)
        {
            switch (@operator)
            {
                case MMExpressions.BinaryOperator.Add:
                    return PromelaBinaryOperator.Add;
                case MMExpressions.BinaryOperator.Subtract:
                    return PromelaBinaryOperator.Min;
                case MMExpressions.BinaryOperator.Multiply:
                    return PromelaBinaryOperator.Mul;
                case MMExpressions.BinaryOperator.Divide:
                    return PromelaBinaryOperator.Div;
                case MMExpressions.BinaryOperator.Modulo:
                    return PromelaBinaryOperator.Mod;
                case MMExpressions.BinaryOperator.LogicalAnd:
                    return PromelaBinaryOperator.And;
                case MMExpressions.BinaryOperator.LogicalOr:
                    return PromelaBinaryOperator.Or;
                case MMExpressions.BinaryOperator.Equals:
                    return PromelaBinaryOperator.Eq;
                case MMExpressions.BinaryOperator.NotEquals:
                    return PromelaBinaryOperator.Neq;
                case MMExpressions.BinaryOperator.LessThan:
                    return PromelaBinaryOperator.Lt;
                case MMExpressions.BinaryOperator.LessThanOrEqual:
                    return PromelaBinaryOperator.Le;
                case MMExpressions.BinaryOperator.GreaterThan:
                    return PromelaBinaryOperator.Gt;
                case MMExpressions.BinaryOperator.GreaterThanOrEqual:
                    return PromelaBinaryOperator.Ge;
                default:
                    throw new NotImplementedException();
            }
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMExpressions.BinaryExpression" />.
        /// </summary>
        /// <param name="binaryExpression">The <see cref="MMExpressions.BinaryExpression" /> instance that should be visited.</param>
        public override PrExpression VisitBinaryExpression(MMExpressions.BinaryExpression binaryExpression)
        {
            Argument.NotNull(binaryExpression, () => binaryExpression);
            var left = binaryExpression.Left.Accept(this);
            var @operator = MmBinOperatorToPrBinOperator(binaryExpression.Operator);
            var right = binaryExpression.Right.Accept(this);
            return new PrExpressions.BinaryExpression(left, @operator, right);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMExpressions.UnaryExpression" />.
        /// </summary>
        /// <param name="unaryExpression">The <see cref="MMExpressions.UnaryExpression" /> instance that should be visited.</param>
        public override PrExpression VisitUnaryExpression(MMExpressions.UnaryExpression unaryExpression)
        {
            Argument.NotNull(unaryExpression, () => unaryExpression);
            var operand = unaryExpression.Operand.Accept(this);
            switch (unaryExpression.Operator)
            {
                case MMExpressions.UnaryOperator.LogicalNot:
                    return new PrExpressions.UnaryExpression(operand, PromelaUnaryOperator.Not);
                case MMExpressions.UnaryOperator.Minus:
                    return new PrExpressions.UnaryExpression(operand, PromelaUnaryOperator.Neg);
                default:
                    throw new NotImplementedException();
            }
        }

        public PrExpressions.VariableReferenceExpression ConvertFieldAccessExpression (MMExpressions.FieldAccessExpression fieldAccessExpression)
        {
            Argument.NotNull(fieldAccessExpression, () => fieldAccessExpression);
            var refName = CommonKnowledge.GetUniqueName(null/* TODO: fieldAccessExpression.Field.SourceSymbol*/);
            return new PrExpressions.VariableReferenceExpression(refName, null, null);
        }

        /// <summary>
        ///     Visits an element of type <see cref="MMExpressions.FieldAccessExpression" />.
        /// </summary>
        /// <param name="fieldAccessExpression">The <see cref="MMExpressions.FieldAccessExpression" /> instance that should be visited.</param>
        public override PrExpression VisitFieldAccessExpression(MMExpressions.FieldAccessExpression fieldAccessExpression)
        {
            Argument.NotNull(fieldAccessExpression, () => fieldAccessExpression);
            return this.ConvertFieldAccessExpression(fieldAccessExpression);
        }
    }

    #endregion

    #region Statements

    internal class MetamodelStatementToPromelaStatement : MetamodelVisitor<PrStatement>
    {
        private MetamodelToPromela CommonKnowledge { get; set; }
        public MetamodelStatementToPromelaStatement(MetamodelToPromela commonKnowledge)
        {
            CommonKnowledge = commonKnowledge;
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMStatements.EmptyStatement" />.
        /// </summary>
        /// <param name="emptyStatement">The <see cref="MMStatements.EmptyStatement" /> instance that should be visited.</param>
        public override PrStatement VisitEmptyStatement(MMStatements.EmptyStatement emptyStatement)
        {
            Argument.NotNull(emptyStatement, () => emptyStatement);
            return new PrStatements.SkipStatement();
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMStatements.BlockStatement" />.
        /// </summary>
        /// <param name="blockStatement">The <see cref="MMStatements.BlockStatement" /> instance that should be visited.</param>
        public override PrStatement VisitBlockStatement(MMStatements.BlockStatement blockStatement)
        {
            Argument.NotNull(blockStatement, () => blockStatement);
            var substatements = blockStatement.Statements.Select(statement => statement.Accept(this)).ToImmutableArray();
            return new PrStatements.SimpleBlockStatement(substatements);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMStatements.ReturnStatement" />.
        /// </summary>
        /// <param name="returnStatement">The <see cref="MMStatements.ReturnStatement" /> instance that should be visited.</param>
        public override PrStatement VisitReturnStatement(MMStatements.ReturnStatement returnStatement)
        {
            Argument.NotNull(returnStatement, () => returnStatement);
            throw new NotImplementedException();
        }

        /// <summary>
        ///   Converts an element of type <see cref="MMStatements.GuardedCommandClause" />.
        /// </summary>
        /// <param name="guardedCommandClause">The <see cref="MMStatements.GuardedCommandClause" /> instance that should be converted.</param>
        public PrStatements.GuardedCommandClause ConvertGuardedCommandClause(MMStatements.GuardedCommandClause guardedCommandClause)
        {
            Argument.NotNull(guardedCommandClause, () => guardedCommandClause);
            var guard = guardedCommandClause.Guard.Accept(CommonKnowledge.ExpressionVisitor);
            var statement = guardedCommandClause.Statement.Accept(this);
            return new PrStatements.GuardedCommandExpressionClause(guard, statement);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMStatements.GuardedCommandStatement" />.
        /// </summary>
        /// <param name="guardedCommandStatement">
        ///   The <see cref="MMStatements.GuardedCommandStatement" /> instance that should be
        ///   visited.
        /// </param>
        public override PrStatement VisitGuardedCommandStatement(MMStatements.GuardedCommandStatement guardedCommandStatement)
        {
            Argument.NotNull(guardedCommandStatement, () => guardedCommandStatement);
            var clauses = guardedCommandStatement.Clauses.Select(ConvertGuardedCommandClause).ToImmutableArray();
            return new PrStatements.GuardedCommandSelectionStatement(clauses);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMStatements.AssignmentStatement" />.
        /// </summary>
        /// <param name="assignmentStatement">The <see cref="MMStatements.AssignmentStatement" /> instance that should be visited.</param>
        public override PrStatement VisitAssignmentStatement(MMStatements.AssignmentStatement assignmentStatement)
        {
            Argument.NotNull(assignmentStatement, () => assignmentStatement);
            // Be careful: http://stackoverflow.com/questions/983030/type-checking-typeof-gettype-or-is
            var stateVar = assignmentStatement.Left as MMExpressions.FieldAccessExpression;

            if (stateVar == null)
            {
                //setter is called or variable is somewhere in the hierarchie.
                throw new NotImplementedException();
            }
            var newVarRef = CommonKnowledge.ExpressionVisitor.ConvertFieldAccessExpression(stateVar);
            var rightExpression = assignmentStatement.Right.Accept(CommonKnowledge.ExpressionVisitor);
            
            return new PrStatements.AssignmentStatement(newVarRef, rightExpression);
        }
    }

    #endregion
}