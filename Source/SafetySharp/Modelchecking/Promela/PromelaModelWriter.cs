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

            proctype.Code.ForEach(stmnt =>
            {
                stmnt.Accept(this);
                codeWriter.NewLine();
            });

            codeWriter.DecreaseIndent();
            codeWriter.AppendLine("}");
        }

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
            return;
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
            return;
        }

        /// <summary>
        ///   Visits an element of type <see cref="VariableReferenceExpression" />.
        /// </summary>
        /// <param name="variableReferenceExpression">The <see cref="VariableReferenceExpression" /> instance that should be visited.</param>
        public override void VisitVariableReferenceExpression(VariableReferenceExpression variableReferenceExpression)
        {
            Assert.ArgumentNotNull(variableReferenceExpression, () => variableReferenceExpression);
            return;
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
            return;
        }

        /// <summary>
        ///   Visits an element of type <see cref="AtomicBlockStatement" />.
        /// </summary>
        /// <param name="atomicBlockStatement">The <see cref="AtomicBlockStatement" /> instance that should be visited.</param>
        public override void VisitAtomicBlockStatement(AtomicBlockStatement atomicBlockStatement)
        {
            Assert.ArgumentNotNull(atomicBlockStatement, () => atomicBlockStatement);
            return;
        }

        /// <summary>
        ///   Visits an element of type <see cref="DStepBlockStatement" />.
        /// </summary>
        /// <param name="dStepBlockStatement">The <see cref="DStepBlockStatement" /> instance that should be visited.</param>
        public override void VisitDStepBlockStatement(DStepBlockStatement dStepBlockStatement)
        {
            Assert.ArgumentNotNull(dStepBlockStatement, () => dStepBlockStatement);
            return;
        }

        /// <summary>
        ///   Visits an element of type <see cref="ReturnStatement" />.
        /// </summary>
        /// <param name="returnStatement">The <see cref="ReturnStatement" /> instance that should be visited.</param>
        public override void VisitReturnStatement(ReturnStatement returnStatement)
        {
            Assert.ArgumentNotNull(returnStatement, () => returnStatement);
            return;
        }

        /// <summary>
        ///   Visits an element of type <see cref="ExpressionStatement" />.
        /// </summary>
        /// <param name="expressionStatement">The <see cref="ExpressionStatement" /> instance that should be visited.</param>
        public override void VisitExpressionStatement(ExpressionStatement expressionStatement)
        {
            Assert.ArgumentNotNull(expressionStatement, () => expressionStatement);
            return;
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
            return;
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
            return;
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
            return;
        }

        /// <summary>
        ///   Visits an element of type <see cref="GuardedCommandElseClause" />.
        /// </summary>
        /// <param name="guardedCommandElseClause">The <see cref="GuardedCommandElseClause" /> instance that should be visited.</param>
        public override void VisitGuardedCommandElseClause(GuardedCommandElseClause guardedCommandElseClause)
        {
            Assert.ArgumentNotNull(guardedCommandElseClause, () => guardedCommandElseClause);
            return;
        }

        /// <summary>
        ///   Visits an element of type <see cref="AssignmentStatement" />.
        /// </summary>
        /// <param name="assignmentStatement">The <see cref="AssignmentStatement" /> instance that should be visited.</param>
        public override void VisitAssignmentStatement(AssignmentStatement assignmentStatement)
        {
            Assert.ArgumentNotNull(assignmentStatement, () => assignmentStatement);
            return;
        }

        /// <summary>
        ///   Visits an element of type <see cref="DeclarationStatement" />.
        /// </summary>
        /// <param name="declarationStatement">The <see cref="DeclarationStatement" /> instance that should be visited.</param>
        public override void VisitDeclarationStatement(DeclarationStatement declarationStatement)
        {
            Assert.ArgumentNotNull(declarationStatement, () => declarationStatement);
            return;
        }

        #endregion

        #endregion
    }
}