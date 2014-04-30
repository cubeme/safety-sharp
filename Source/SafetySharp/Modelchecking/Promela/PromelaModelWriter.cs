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
    using System.Text;
    using SafetySharp.Modelchecking.Promela.Expressions;
    using SafetySharp.Modelchecking.Promela.Statements;
    using Utilities;


    internal class PromelaModelWriter : PromelaVisitor<string>
    {

        #region Proctype

        /// <summary>
        ///     Visits an element of type <see cref="Proctype" />.
        /// </summary>
        /// <param name="proctype">The <see cref="Proctype" /> instance that should be visited.</param>
        public override string VisitProctype(Proctype proctype)
        {
            // Goal: 
            // 'proctype' name '('')''{'
            //      sequence
            // '}'

            Assert.ArgumentNotNull(proctype, () => proctype);

            var codeStrings = new List<string>();

            foreach (var code in proctype.Code)
            {
                codeStrings.Add(code.Accept(this));
            }

            var proctypeString = "proctype " + proctype.Name + "( ) {\n" + String.Join("\n", codeStrings)+ "\n}";

            return proctypeString;
        }
        #endregion

        #region Expressions
        /// <summary>
        ///     Visits an element of type <see cref="BooleanLiteral" />.
        /// </summary>
        /// <param name="booleanLiteral">The <see cref="BooleanLiteral" /> instance that should be visited.</param>
        public override string VisitBooleanLiteral(BooleanLiteral booleanLiteral)
        {
            Assert.ArgumentNotNull(booleanLiteral, () => booleanLiteral);
            return default(string);
        }
        /// <summary>
        ///     Visits an element of type <see cref="NumberLiteral" />.
        /// </summary>
        /// <param name="numberLiteral">The <see cref="NumberLiteral" /> instance that should be visited.</param>
        public override string VisitNumberLiteral(NumberLiteral numberLiteral)
        {
            Assert.ArgumentNotNull(numberLiteral, () => numberLiteral);
            return default(string);
        }

        /// <summary>
        ///     Visits an element of type <see cref="SkipLiteral" />.
        /// </summary>
        /// <param name="skipLiteral">The <see cref="SkipLiteral" /> instance that should be visited.</param>
        public override string VisitSkipLiteral(SkipLiteral skipLiteral)
        {
            Assert.ArgumentNotNull(skipLiteral, () => skipLiteral);
            return default(string);
        }

        /// <summary>
        ///     Visits an element of type <see cref="BinaryExpression" />.
        /// </summary>
        /// <param name="binaryExpression">The <see cref="BinaryExpression" /> instance that should be visited.</param>
        public override string VisitBinaryExpression(BinaryExpression binaryExpression)
        {
            Assert.ArgumentNotNull(binaryExpression, () => binaryExpression);
            return default(string);
        }

        /// <summary>
        ///     Visits an element of type <see cref="UnaryExpression" />.
        /// </summary>
        /// <param name="unaryExpression">The <see cref="UnaryExpression" /> instance that should be visited.</param>
        public override string VisitUnaryExpression(UnaryExpression unaryExpression)
        {
            Assert.ArgumentNotNull(unaryExpression, () => unaryExpression);
            return default(string);
        }

        /// <summary>
        ///     Visits an element of type <see cref="VariableReferenceExpression" />.
        /// </summary>
        /// <param name="variableReferenceExpression">The <see cref="VariableReferenceExpression" /> instance that should be visited.</param>
        public override string VisitVariableReferenceExpression(VariableReferenceExpression variableReferenceExpression)
        {
            Assert.ArgumentNotNull(variableReferenceExpression, () => variableReferenceExpression);
            return default(string);
        }
        #endregion

        #region Statements
        /// <summary>
        ///     Visits an element of type <see cref="SimpleBlockStatement" />.
        /// </summary>
        /// <param name="simpleBlockStatement">The <see cref="SimpleBlockStatement" /> instance that should be visited.</param>
        public override string VisitSimpleBlockStatement(SimpleBlockStatement simpleBlockStatement)
        {
            Assert.ArgumentNotNull(simpleBlockStatement, () => simpleBlockStatement);
            return default(string);
        }

        /// <summary>
        ///     Visits an element of type <see cref="AtomicBlockStatement" />.
        /// </summary>
        /// <param name="atomicBlockStatement">The <see cref="AtomicBlockStatement" /> instance that should be visited.</param>
        public override string VisitAtomicBlockStatement(AtomicBlockStatement atomicBlockStatement)
        {
            Assert.ArgumentNotNull(atomicBlockStatement, () => atomicBlockStatement);
            return default(string);
        }

        /// <summary>
        ///     Visits an element of type <see cref="DStepBlockStatement" />.
        /// </summary>
        /// <param name="dStepBlockStatement">The <see cref="DStepBlockStatement" /> instance that should be visited.</param>
        public override string VisitDStepBlockStatement(DStepBlockStatement dStepBlockStatement)
        {
            Assert.ArgumentNotNull(dStepBlockStatement, () => dStepBlockStatement);
            return default(string);
        }

        /// <summary>
        ///     Visits an element of type <see cref="ReturnStatement" />.
        /// </summary>
        /// <param name="returnStatement">The <see cref="ReturnStatement" /> instance that should be visited.</param>
        public override string VisitReturnStatement(ReturnStatement returnStatement)
        {
            Assert.ArgumentNotNull(returnStatement, () => returnStatement);
            return default(string);
        }

        /// <summary>
        ///     Visits an element of type <see cref="ExpressionStatement" />.
        /// </summary>
        /// <param name="expressionStatement">The <see cref="ExpressionStatement" /> instance that should be visited.</param>
        public override string VisitExpressionStatement(ExpressionStatement expressionStatement)
        {
            Assert.ArgumentNotNull(expressionStatement, () => expressionStatement);
            return default(string);
        }

        /// <summary>
        ///     Visits an element of type <see cref="GuardedCommandRepetitionStatement" />.
        /// </summary>
        /// <param name="guardedCommandRepetitionStatement">The <see cref="GuardedCommandRepetitionStatement" /> instance that should be visited.</param>
        public override string VisitGuardedCommandRepetitionStatement(GuardedCommandRepetitionStatement guardedCommandRepetitionStatement)
        {
            Assert.ArgumentNotNull(guardedCommandRepetitionStatement, () => guardedCommandRepetitionStatement);
            return default(string);
        }

        /// <summary>
        ///     Visits an element of type <see cref="GuardedCommandSelectionStatement" />.
        /// </summary>
        /// <param name="guardedCommandSelectionStatement">The <see cref="GuardedCommandSelectionStatement" /> instance that should be visited.</param>
        public override string VisitGuardedCommandSelectionStatement(GuardedCommandSelectionStatement guardedCommandSelectionStatement)
        {
            Assert.ArgumentNotNull(guardedCommandSelectionStatement, () => guardedCommandSelectionStatement);
            return default(string);
        }

        /// <summary>
        ///     Visits an element of type <see cref="GuardedCommandExpressionClause" />.
        /// </summary>
        /// <param name="guardedCommandExpressionClause">The <see cref="GuardedCommandExpressionClause" /> instance that should be visited.</param>
        public override string VisitGuardedCommandExpressionClause(GuardedCommandExpressionClause guardedCommandExpressionClause)
        {
            Assert.ArgumentNotNull(guardedCommandExpressionClause, () => guardedCommandExpressionClause);
            return default(string);
        }

        /// <summary>
        ///     Visits an element of type <see cref="GuardedCommandElseClause" />.
        /// </summary>
        /// <param name="guardedCommandElseClause">The <see cref="GuardedCommandElseClause" /> instance that should be visited.</param>
        public override string VisitGuardedCommandElseClause(GuardedCommandElseClause guardedCommandElseClause)
        {
            Assert.ArgumentNotNull(guardedCommandElseClause, () => guardedCommandElseClause);
            return default(string);
        }

        /// <summary>
        ///     Visits an element of type <see cref="AssignmentStatement" />.
        /// </summary>
        /// <param name="assignmentStatement">The <see cref="AssignmentStatement" /> instance that should be visited.</param>
        public override string VisitAssignmentStatement(AssignmentStatement assignmentStatement)
        {
            Assert.ArgumentNotNull(assignmentStatement, () => assignmentStatement);
            return default(string);
        }

        /// <summary>
        ///     Visits an element of type <see cref="DeclarationStatement" />.
        /// </summary>
        /// <param name="declarationStatement">The <see cref="DeclarationStatement" /> instance that should be visited.</param>
        public override string VisitDeclarationStatement(DeclarationStatement declarationStatement)
        {
            Assert.ArgumentNotNull(declarationStatement, () => declarationStatement);
            return default(string);
        }
        #endregion

    }
}