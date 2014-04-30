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
    using Expressions;
    using Statements;
    using Utilities;

    internal static class PromelaExtensionMethods
    {
        public static void ForEach<T>(this IEnumerable<T> source, Action<T> action)
        {
            foreach (T element in source)
                action(element);
        }
    }

    internal class PromelaModelWriter : PromelaVisitor
    {
        private readonly CodeWriter codeWriter = new CodeWriter();

        #region Proctype

        /// <summary>
        ///   Visits an element of type <see cref="Proctype" />.
        /// </summary>
        /// <param name="proctype">The <see cref="Proctype" /> instance that should be visited.</param>
        public override void VisitProctype(Proctype proctype)
        {
            // 'proctype' name '('')''{'
            //      sequence
            // '}'

            Assert.ArgumentNotNull(proctype, () => proctype);

            codeWriter.AppendLine("proctype " + proctype.Name + "() {");
            codeWriter.IncreaseIndent();
            proctype.Code.ForEach(stmnt => stmnt.Accept(this));
            codeWriter.DecreaseIndent();
            codeWriter.AppendLine("}");
        }

        #endregion

        #region Expressions

        /// <summary>
        ///   Visits an element of type <see cref="BooleanLiteral" />.
        /// </summary>
        /// <param name="booleanLiteral">The <see cref="BooleanLiteral" /> instance that should be visited.</param>
        public override void VisitBooleanLiteral(BooleanLiteral booleanLiteral)
        {
            Assert.ArgumentNotNull(booleanLiteral, () => booleanLiteral);

            switch (booleanLiteral.Value)
            {
                case true:
                    codeWriter.Append("true");
                    break;
                case false:
                    codeWriter.Append("false");
                    break;
            }
        }

        /// <summary>
        ///   Visits an element of type <see cref="NumberLiteral" />.
        /// </summary>
        /// <param name="numberLiteral">The <see cref="NumberLiteral" /> instance that should be visited.</param>
        public override void VisitNumberLiteral(NumberLiteral numberLiteral)
        {
            Assert.ArgumentNotNull(numberLiteral, () => numberLiteral);
            codeWriter.Append(numberLiteral.Value.ToString());
        }

        /// <summary>
        ///   Visits an element of type <see cref="SkipLiteral" />.
        /// </summary>
        /// <param name="skipLiteral">The <see cref="SkipLiteral" /> instance that should be visited.</param>
        public override void VisitSkipLiteral(SkipLiteral skipLiteral)
        {
            Assert.ArgumentNotNull(skipLiteral, () => skipLiteral);
            codeWriter.Append("skip");
        }

        /// <summary>
        ///   Visits an element of type <see cref="BinaryExpression" />.
        /// </summary>
        /// <param name="binaryExpression">The <see cref="BinaryExpression" /> instance that should be visited.</param>
        public override void VisitBinaryExpression(BinaryExpression binaryExpression)
        {
            Assert.ArgumentNotNull(binaryExpression, () => binaryExpression);
            codeWriter.Append("(");
            binaryExpression.Left.Accept(this);

            switch (binaryExpression.Operator)
            {
                case PromelaBinaryOperator.And:
                    codeWriter.Append("&&");
                    break;
                case PromelaBinaryOperator.Or:
                    codeWriter.Append("||");
                    break;
                case PromelaBinaryOperator.Add:
                    codeWriter.Append("+");
                    break;
                case PromelaBinaryOperator.Min:
                    codeWriter.Append("-");
                    break;
                case PromelaBinaryOperator.Mul:
                    codeWriter.Append("*");
                    break;
                case PromelaBinaryOperator.Div:
                    codeWriter.Append("/");
                    break;
                case PromelaBinaryOperator.Mod:
                    codeWriter.Append("%");
                    break;
                case PromelaBinaryOperator.BAnd:
                    codeWriter.Append("&");
                    break;
                case PromelaBinaryOperator.Xor:
                    codeWriter.Append("^");
                    break;
                case PromelaBinaryOperator.BOr:
                    codeWriter.Append("|");
                    break;
                case PromelaBinaryOperator.Gt:
                    codeWriter.Append(">");
                    break;
                case PromelaBinaryOperator.Lt:
                    codeWriter.Append(">");
                    break;
                case PromelaBinaryOperator.Ge:
                    codeWriter.Append(">=");
                    break;
                case PromelaBinaryOperator.Le:
                    codeWriter.Append("<=");
                    break;
                case PromelaBinaryOperator.Eq:
                    codeWriter.Append("==");
                    break;
                case PromelaBinaryOperator.Neq:
                    codeWriter.Append("!=");
                    break;
                case PromelaBinaryOperator.Bls:
                    codeWriter.Append("<<");
                    break;
                case PromelaBinaryOperator.Brs:
                    codeWriter.Append(">>");
                    break;
            }

            binaryExpression.Right.Accept(this);
            codeWriter.Append(")");
        }

        /// <summary>
        ///   Visits an element of type <see cref="UnaryExpression" />.
        /// </summary>
        /// <param name="unaryExpression">The <see cref="UnaryExpression" /> instance that should be visited.</param>
        public override void VisitUnaryExpression(UnaryExpression unaryExpression)
        {
            Assert.ArgumentNotNull(unaryExpression, () => unaryExpression);
            codeWriter.Append("(");
            switch (unaryExpression.Operator)
            {
                case PromelaUnaryOperator.Neg:
                    codeWriter.Append("-");
                    break;
                case PromelaUnaryOperator.Not:
                    codeWriter.Append("!");
                    break;
                case PromelaUnaryOperator.Tilde:
                    codeWriter.Append("~");
                    break;
            }
            unaryExpression.Expression.Accept(this);
            codeWriter.Append(")");
        }

        /// <summary>
        ///   Visits an element of type <see cref="VariableReferenceExpression" />.
        /// </summary>
        /// <param name="variableReferenceExpression">The <see cref="VariableReferenceExpression" /> instance that should be visited.</param>
        public override void VisitVariableReferenceExpression(VariableReferenceExpression variableReferenceExpression)
        {
            // varref : name [ '[' any_expr ']' ] [ '.' varref ]
            Assert.ArgumentNotNull(variableReferenceExpression, () => variableReferenceExpression);

            codeWriter.Append(variableReferenceExpression.Identifier);
            if (variableReferenceExpression.Index != null)
            {
                codeWriter.Append("[");
                variableReferenceExpression.Index.Accept(this);
                codeWriter.Append("]");
            }
            if (variableReferenceExpression.Member != null)
            {
                codeWriter.Append(".");
                variableReferenceExpression.Member.Accept(this);
            }
        }

        #endregion

        #region Statements

        /// <summary>
        ///   Visits an element of type <see cref="SimpleBlockStatement" />.
        /// </summary>
        /// <param name="simpleBlockStatement">The <see cref="SimpleBlockStatement" /> instance that should be visited.</param>
        public override void VisitSimpleBlockStatement(SimpleBlockStatement simpleBlockStatement)
        {
            Assert.ArgumentNotNull(simpleBlockStatement, () => simpleBlockStatement);
            codeWriter.AppendLine("{");
            codeWriter.IncreaseIndent();
            simpleBlockStatement.Statements.ForEach(stmnt => stmnt.Accept(this));
            codeWriter.DecreaseIndent();
            codeWriter.AppendLine("}");
        }

        /// <summary>
        ///   Visits an element of type <see cref="AtomicBlockStatement" />.
        /// </summary>
        /// <param name="atomicBlockStatement">The <see cref="AtomicBlockStatement" /> instance that should be visited.</param>
        public override void VisitAtomicBlockStatement(AtomicBlockStatement atomicBlockStatement)
        {
            Assert.ArgumentNotNull(atomicBlockStatement, () => atomicBlockStatement);
            codeWriter.AppendLine("atomic {");
            codeWriter.IncreaseIndent();
            atomicBlockStatement.Statements.ForEach(stmnt => stmnt.Accept(this));
            codeWriter.DecreaseIndent();
            codeWriter.AppendLine("}");
        }

        /// <summary>
        ///   Visits an element of type <see cref="DStepBlockStatement" />.
        /// </summary>
        /// <param name="dStepBlockStatement">The <see cref="DStepBlockStatement" /> instance that should be visited.</param>
        public override void VisitDStepBlockStatement(DStepBlockStatement dStepBlockStatement)
        {
            Assert.ArgumentNotNull(dStepBlockStatement, () => dStepBlockStatement);
            codeWriter.AppendLine("d_step {");
            codeWriter.IncreaseIndent();
            dStepBlockStatement.Statements.ForEach(stmnt => stmnt.Accept(this));
            codeWriter.DecreaseIndent();
            codeWriter.AppendLine("}");
        }

        /// <summary>
        ///   Visits an element of type <see cref="ReturnStatement" />.
        /// </summary>
        /// <param name="returnStatement">The <see cref="ReturnStatement" /> instance that should be visited.</param>
        public override void VisitReturnStatement(ReturnStatement returnStatement)
        {
            Assert.ArgumentNotNull(returnStatement, () => returnStatement);
            codeWriter.Append("return ");
            returnStatement.Expression.Accept(this);
            codeWriter.Append(";");
            codeWriter.NewLine();
        }

        /// <summary>
        ///   Visits an element of type <see cref="ExpressionStatement" />.
        /// </summary>
        /// <param name="expressionStatement">The <see cref="ExpressionStatement" /> instance that should be visited.</param>
        public override void VisitExpressionStatement(ExpressionStatement expressionStatement)
        {
            Assert.ArgumentNotNull(expressionStatement, () => expressionStatement);
            expressionStatement.Expression.Accept(this);
            codeWriter.Append(";");
            codeWriter.NewLine();
        }

        /// <summary>
        ///   Visits an element of type <see cref="GuardedCommandRepetitionStatement" />.
        /// </summary>
        /// <param name="guardedCommandRepetitionStatement">
        ///   The <see cref="GuardedCommandRepetitionStatement" /> instance that should be
        ///   visited.
        /// </param>
        public override void VisitGuardedCommandRepetitionStatement(GuardedCommandRepetitionStatement guardedCommandRepetitionStatement)
        {
            Assert.ArgumentNotNull(guardedCommandRepetitionStatement, () => guardedCommandRepetitionStatement);
            codeWriter.AppendLine("do");
            guardedCommandRepetitionStatement.Clauses.ForEach(clause => clause.Accept(this));
            codeWriter.AppendLine("od");
        }

        /// <summary>
        ///   Visits an element of type <see cref="GuardedCommandSelectionStatement" />.
        /// </summary>
        /// <param name="guardedCommandSelectionStatement">
        ///   The <see cref="GuardedCommandSelectionStatement" /> instance that should be
        ///   visited.
        /// </param>
        public override void VisitGuardedCommandSelectionStatement(GuardedCommandSelectionStatement guardedCommandSelectionStatement)
        {
            Assert.ArgumentNotNull(guardedCommandSelectionStatement, () => guardedCommandSelectionStatement);
            codeWriter.AppendLine("if");
            guardedCommandSelectionStatement.Clauses.ForEach(clause => clause.Accept(this));
            codeWriter.AppendLine("fi");
        }

        /// <summary>
        ///   Visits an element of type <see cref="GuardedCommandExpressionClause" />.
        /// </summary>
        /// <param name="guardedCommandExpressionClause">
        ///   The <see cref="GuardedCommandExpressionClause" /> instance that should be
        ///   visited.
        /// </param>
        public override void VisitGuardedCommandExpressionClause(GuardedCommandExpressionClause guardedCommandExpressionClause)
        {
            Assert.ArgumentNotNull(guardedCommandExpressionClause, () => guardedCommandExpressionClause);
            codeWriter.Append("::\t");
            guardedCommandExpressionClause.Guard.Accept(this);
            codeWriter.Append(" ->");
            codeWriter.IncreaseIndent();
            codeWriter.NewLine();
            guardedCommandExpressionClause.Statement.Accept(this);
            codeWriter.DecreaseIndent();
        }

        /// <summary>
        ///   Visits an element of type <see cref="GuardedCommandElseClause" />.
        /// </summary>
        /// <param name="guardedCommandElseClause">The <see cref="GuardedCommandElseClause" /> instance that should be visited.</param>
        public override void VisitGuardedCommandElseClause(GuardedCommandElseClause guardedCommandElseClause)
        {
            Assert.ArgumentNotNull(guardedCommandElseClause, () => guardedCommandElseClause);
            codeWriter.AppendLine("::\telse ->");
            guardedCommandElseClause.Statement.Accept(this);
            codeWriter.DecreaseIndent();
        }

        /// <summary>
        ///   Visits an element of type <see cref="AssignmentStatement" />.
        /// </summary>
        /// <param name="assignmentStatement">The <see cref="AssignmentStatement" /> instance that should be visited.</param>
        public override void VisitAssignmentStatement(AssignmentStatement assignmentStatement)
        {
            Assert.ArgumentNotNull(assignmentStatement, () => assignmentStatement);
            assignmentStatement.Left.Accept(this);
            codeWriter.Append(" = ");
            assignmentStatement.Right.Accept(this);
            codeWriter.AppendLine(";");
        }

        /// <summary>
        ///   Visits an element of type <see cref="DeclarationStatement" />.
        /// </summary>
        /// <param name="declarationStatement">The <see cref="DeclarationStatement" /> instance that should be visited.</param>
        public override void VisitDeclarationStatement(DeclarationStatement declarationStatement)
        {
            // one_decl : typename name [ '[' const ']' ] [ '=' any_expr ]
            Assert.ArgumentNotNull(declarationStatement, () => declarationStatement);
            switch (declarationStatement.Type)
            {
                case PromelaTypeName.Bit:
                    codeWriter.Append("bit");
                    break;
                case PromelaTypeName.Bool:
                    codeWriter.Append("bool");
                    break;
                case PromelaTypeName.Byte:
                    codeWriter.Append("byte");
                    break;
                case PromelaTypeName.Short:
                    codeWriter.Append("short");
                    break;
                case PromelaTypeName.Int:
                    codeWriter.Append("int");
                    break;
                case PromelaTypeName.Mtype:
                    codeWriter.Append("m_type");
                    break;
                case PromelaTypeName.Chan:
                    codeWriter.Append("chan");
                    break;
                case PromelaTypeName.Pid:
                    codeWriter.Append("pit");
                    break;
            }
            codeWriter.Append(" ");
            if (declarationStatement.ArraySize != 0)
            {
                codeWriter.Append("[");
                codeWriter.AppendLine(declarationStatement.ArraySize.ToString());
                codeWriter.Append("]");
            }
            if (declarationStatement.InitialValue != null)
            {
                codeWriter.Append(" = ");
                declarationStatement.InitialValue.Accept(this);
            }
            codeWriter.AppendLine(";");
        }

        #endregion
    }
}