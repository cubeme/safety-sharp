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


// Note: http://spinroot.com/spin/Man/separators.html
//       http://spinroot.com/spin/Man/grammar.html
//       semicolon ";" and arrow "->" are statement separators and not statement terminators!

namespace SafetySharp.Modelchecking.Promela
{
    using System;
    using System.Collections.Generic;
    using Expressions;
    using Formula;
    using Modeling;
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
        public PromelaModelWriter()
        {
            CodeWriter = new CodeWriter();
        }

        public PromelaModelWriter(bool skipHeader)
        {
            if (skipHeader)
            {
                CodeWriter = new CodeWriter(null);
            }
            else
            {
                CodeWriter = new CodeWriter();
            }
        }

        public readonly CodeWriter CodeWriter;

        #region Proctype and LtlFormula

        /// <summary>
        ///   Visits an element of type <see cref="Proctype" />.
        /// </summary>
        /// <param name="proctype">The <see cref="Proctype" /> instance that should be visited.</param>
        public override void VisitProctype(Proctype proctype)
        {
            // 'active' 'proctype' name '('')''{'
            //      sequence
            // '}'

            Argument.NotNull(proctype, () => proctype);

            CodeWriter.AppendLine("active proctype " + proctype.Name + "() {{");
            CodeWriter.IncreaseIndent();
            var first = true;
            foreach (var statement in proctype.Code)
            {
                if (!first)
                    CodeWriter.AppendLine(";");
                statement.Accept(this);
                first = false;
            }
            CodeWriter.DecreaseIndent();
            CodeWriter.AppendLine("}}");
        }

        /// <summary>
        ///     Visits an element of type <see cref="LtlFormula" />.
        /// </summary>
        /// <param name="ltlFormula">The <see cref="LtlFormula" /> instance that should be visited.</param>
        // http://spinroot.com/spin/Man/ltl.html
        public override void VisitLtlFormula(LtlFormula ltlFormula)
        {
            Argument.NotNull(ltlFormula, () => ltlFormula);

            CodeWriter.Append("ltl ");
            if (ltlFormula.Name!=null)
                CodeWriter.Append("{0} ",ltlFormula.Name);

            CodeWriter.Append("{{ ");
            ltlFormula.Formula.Accept(this);
            CodeWriter.Append(" }}");
            CodeWriter.NewLine();
        }

        #endregion

        #region Expressions

        /// <summary>
        ///   Visits an element of type <see cref="BooleanLiteral" />.
        /// </summary>
        /// <param name="booleanLiteral">The <see cref="BooleanLiteral" /> instance that should be visited.</param>
        public override void VisitBooleanLiteral(BooleanLiteral booleanLiteral)
        {
            Argument.NotNull(booleanLiteral, () => booleanLiteral);

            switch (booleanLiteral.Value)
            {
                case true:
                    CodeWriter.Append("true");
                    break;
                case false:
                    CodeWriter.Append("false");
                    break;
            }
        }

        /// <summary>
        ///   Visits an element of type <see cref="NumberLiteral" />.
        /// </summary>
        /// <param name="numberLiteral">The <see cref="NumberLiteral" /> instance that should be visited.</param>
        public override void VisitNumberLiteral(NumberLiteral numberLiteral)
        {
            Argument.NotNull(numberLiteral, () => numberLiteral);
            CodeWriter.Append(numberLiteral.Value.ToString());
        }

        /// <summary>
        ///   Visits an element of type <see cref="BinaryExpression" />.
        /// </summary>
        /// <param name="binaryExpression">The <see cref="BinaryExpression" /> instance that should be visited.</param>
        public override void VisitBinaryExpression(BinaryExpression binaryExpression)
        {
            Argument.NotNull(binaryExpression, () => binaryExpression);
            CodeWriter.Append("(");
            binaryExpression.Left.Accept(this);

            switch (binaryExpression.Operator)
            {
                case PromelaBinaryOperator.And:
                    CodeWriter.Append("&&");
                    break;
                case PromelaBinaryOperator.Or:
                    CodeWriter.Append("||");
                    break;
                case PromelaBinaryOperator.Add:
                    CodeWriter.Append("+");
                    break;
                case PromelaBinaryOperator.Min:
                    CodeWriter.Append("-");
                    break;
                case PromelaBinaryOperator.Mul:
                    CodeWriter.Append("*");
                    break;
                case PromelaBinaryOperator.Div:
                    CodeWriter.Append("/");
                    break;
                case PromelaBinaryOperator.Mod:
                    CodeWriter.Append("%");
                    break;
                case PromelaBinaryOperator.BAnd:
                    CodeWriter.Append("&");
                    break;
                case PromelaBinaryOperator.Xor:
                    CodeWriter.Append("^");
                    break;
                case PromelaBinaryOperator.BOr:
                    CodeWriter.Append("|");
                    break;
                case PromelaBinaryOperator.Gt:
                    CodeWriter.Append(">");
                    break;
                case PromelaBinaryOperator.Lt:
                    CodeWriter.Append(">");
                    break;
                case PromelaBinaryOperator.Ge:
                    CodeWriter.Append(">=");
                    break;
                case PromelaBinaryOperator.Le:
                    CodeWriter.Append("<=");
                    break;
                case PromelaBinaryOperator.Eq:
                    CodeWriter.Append("==");
                    break;
                case PromelaBinaryOperator.Neq:
                    CodeWriter.Append("!=");
                    break;
                case PromelaBinaryOperator.Bls:
                    CodeWriter.Append("<<");
                    break;
                case PromelaBinaryOperator.Brs:
                    CodeWriter.Append(">>");
                    break;
            }

            binaryExpression.Right.Accept(this);
            CodeWriter.Append(")");
        }

        /// <summary>
        ///   Visits an element of type <see cref="UnaryExpression" />.
        /// </summary>
        /// <param name="unaryExpression">The <see cref="UnaryExpression" /> instance that should be visited.</param>
        public override void VisitUnaryExpression(UnaryExpression unaryExpression)
        {
            Argument.NotNull(unaryExpression, () => unaryExpression);
            CodeWriter.Append("(");
            switch (unaryExpression.Operator)
            {
                case PromelaUnaryOperator.Neg:
                    CodeWriter.Append("-");
                    break;
                case PromelaUnaryOperator.Not:
                    CodeWriter.Append("!");
                    break;
                case PromelaUnaryOperator.Tilde:
                    CodeWriter.Append("~");
                    break;
            }
            unaryExpression.Expression.Accept(this);
            CodeWriter.Append(")");
        }

        /// <summary>
        ///   Visits an element of type <see cref="VariableReferenceExpression" />.
        /// </summary>
        /// <param name="variableReferenceExpression">The <see cref="VariableReferenceExpression" /> instance that should be visited.</param>
        public override void VisitVariableReferenceExpression(VariableReferenceExpression variableReferenceExpression)
        {
            // varref : name [ '[' any_expr ']' ] [ '.' varref ]
            Argument.NotNull(variableReferenceExpression, () => variableReferenceExpression);

            CodeWriter.Append(variableReferenceExpression.Identifier);
            if (variableReferenceExpression.Index != null)
            {
                CodeWriter.Append("[");
                variableReferenceExpression.Index.Accept(this);
                CodeWriter.Append("]");
            }
            if (variableReferenceExpression.Member != null)
            {
                CodeWriter.Append(".");
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
            Argument.NotNull(simpleBlockStatement, () => simpleBlockStatement);
            CodeWriter.AppendLine("{{");
            CodeWriter.IncreaseIndent();
            var first = true;
            foreach (var statement in simpleBlockStatement.Statements)
            {
                if (!first)
                    CodeWriter.AppendLine(";");
                statement.Accept(this);
                first = false;
            }
            CodeWriter.NewLine();
            CodeWriter.DecreaseIndent();
            CodeWriter.Append("}}");
        }

        /// <summary>
        ///   Visits an element of type <see cref="AtomicBlockStatement" />.
        /// </summary>
        /// <param name="atomicBlockStatement">The <see cref="AtomicBlockStatement" /> instance that should be visited.</param>
        public override void VisitAtomicBlockStatement(AtomicBlockStatement atomicBlockStatement)
        {
            Argument.NotNull(atomicBlockStatement, () => atomicBlockStatement);
            CodeWriter.AppendLine("atomic {{");
            CodeWriter.IncreaseIndent();
            var first = true;
            foreach (var statement in atomicBlockStatement.Statements)
            {
                if (!first)
                    CodeWriter.AppendLine(";");
                statement.Accept(this);
                first = false;
            }
            CodeWriter.NewLine();
            CodeWriter.DecreaseIndent();
            CodeWriter.Append("}}");
        }

        /// <summary>
        ///   Visits an element of type <see cref="DStepBlockStatement" />.
        /// </summary>
        /// <param name="dStepBlockStatement">The <see cref="DStepBlockStatement" /> instance that should be visited.</param>
        public override void VisitDStepBlockStatement(DStepBlockStatement dStepBlockStatement)
        {
            Argument.NotNull(dStepBlockStatement, () => dStepBlockStatement);
            CodeWriter.AppendLine("d_step {{");
            CodeWriter.IncreaseIndent();
            var first = true;
            foreach (var statement in dStepBlockStatement.Statements)
            {
                if (!first)
                    CodeWriter.AppendLine(";");
                statement.Accept(this);
                first = false;
            }
            CodeWriter.NewLine();
            CodeWriter.DecreaseIndent();
            CodeWriter.Append("}}");
        }

        /// <summary>
        ///   Visits an element of type <see cref="ReturnStatement" />.
        /// </summary>
        /// <param name="returnStatement">The <see cref="ReturnStatement" /> instance that should be visited.</param>
        public override void VisitReturnStatement(ReturnStatement returnStatement)
        {
            Argument.NotNull(returnStatement, () => returnStatement);
            CodeWriter.Append("return ");
            returnStatement.Expression.Accept(this);
            CodeWriter.NewLine();
        }

        /// <summary>
        ///   Visits an element of type <see cref="ExpressionStatement" />.
        /// </summary>
        /// <param name="expressionStatement">The <see cref="ExpressionStatement" /> instance that should be visited.</param>
        public override void VisitExpressionStatement(ExpressionStatement expressionStatement)
        {
            Argument.NotNull(expressionStatement, () => expressionStatement);
            CodeWriter.Append("(");
            expressionStatement.Expression.Accept(this);
            CodeWriter.Append(")");
        }

        /// <summary>
        ///   Visits an element of type <see cref="SkipStatement" />.
        /// </summary>
        /// <param name="skipStatement">The <see cref="SkipStatement" /> instance that should be visited.</param>
        public override void VisitSkipStatement(SkipStatement skipStatement)
        {
            Argument.NotNull(skipStatement, () => skipStatement);
            CodeWriter.Append("skip");
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
            Argument.NotNull(guardedCommandRepetitionStatement, () => guardedCommandRepetitionStatement);
            CodeWriter.AppendLine("do");
            guardedCommandRepetitionStatement.Clauses.ForEach(clause => clause.Accept(this));
            CodeWriter.AppendLine("od");
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
            Argument.NotNull(guardedCommandSelectionStatement, () => guardedCommandSelectionStatement);
            CodeWriter.AppendLine("if");
            guardedCommandSelectionStatement.Clauses.ForEach(clause => clause.Accept(this));
            CodeWriter.Append("fi");
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
            Argument.NotNull(guardedCommandExpressionClause, () => guardedCommandExpressionClause);
            CodeWriter.Append("::\t");
            guardedCommandExpressionClause.Guard.Accept(this);
            CodeWriter.Append(" ->");
            CodeWriter.IncreaseIndent();
            CodeWriter.NewLine();
            guardedCommandExpressionClause.Statement.Accept(this);

            CodeWriter.NewLine();
            CodeWriter.DecreaseIndent();
        }

        /// <summary>
        ///   Visits an element of type <see cref="GuardedCommandElseClause" />.
        /// </summary>
        /// <param name="guardedCommandElseClause">The <see cref="GuardedCommandElseClause" /> instance that should be visited.</param>
        public override void VisitGuardedCommandElseClause(GuardedCommandElseClause guardedCommandElseClause)
        {
            Argument.NotNull(guardedCommandElseClause, () => guardedCommandElseClause);
            CodeWriter.AppendLine("::\telse ->");
            guardedCommandElseClause.Statement.Accept(this);
            CodeWriter.DecreaseIndent();
        }

        /// <summary>
        ///   Visits an element of type <see cref="AssignmentStatement" />.
        /// </summary>
        /// <param name="assignmentStatement">The <see cref="AssignmentStatement" /> instance that should be visited.</param>
        public override void VisitAssignmentStatement(AssignmentStatement assignmentStatement)
        {
            Argument.NotNull(assignmentStatement, () => assignmentStatement);
            assignmentStatement.Left.Accept(this);
            CodeWriter.Append(" = ");
            assignmentStatement.Right.Accept(this);
        }

        /// <summary>
        ///   Visits an element of type <see cref="DeclarationStatement" />.
        /// </summary>
        /// <param name="declarationStatement">The <see cref="DeclarationStatement" /> instance that should be visited.</param>
        public override void VisitDeclarationStatement(DeclarationStatement declarationStatement)
        {
            // one_decl : typename name [ '[' const ']' ] [ '=' any_expr ]
            Argument.NotNull(declarationStatement, () => declarationStatement);
            switch (declarationStatement.Type)
            {
                case PromelaTypeName.Bit:
                    CodeWriter.Append("bit");
                    break;
                case PromelaTypeName.Bool:
                    CodeWriter.Append("bool");
                    break;
                case PromelaTypeName.Byte:
                    CodeWriter.Append("byte");
                    break;
                case PromelaTypeName.Short:
                    CodeWriter.Append("short");
                    break;
                case PromelaTypeName.Int:
                    CodeWriter.Append("int");
                    break;
                case PromelaTypeName.Mtype:
                    CodeWriter.Append("m_type");
                    break;
                case PromelaTypeName.Chan:
                    CodeWriter.Append("chan");
                    break;
                case PromelaTypeName.Pid:
                    CodeWriter.Append("pit");
                    break;
            }
            CodeWriter.Append(" ");
            CodeWriter.Append(declarationStatement.Identifier);
            CodeWriter.Append(" ");
            if (declarationStatement.ArraySize > 1)
            {
                CodeWriter.Append("[");
                CodeWriter.Append(declarationStatement.ArraySize.ToString());
                CodeWriter.Append("]");
            }
            if (declarationStatement.InitialValue != null)
            {
                CodeWriter.Append(" = ");
                declarationStatement.InitialValue.Accept(this);
            }
        }

        #endregion

        #region Formula

        /// <summary>
        ///     Visits an element of type <see cref="PropositionalStateFormula" />.
        /// </summary>
        /// <param name="propositionalStateFormula">The <see cref="PropositionalStateFormula" /> instance that should be visited.</param>
        public override void VisitPropositionalStateFormula(PropositionalStateFormula propositionalStateFormula)
        {
            Argument.NotNull(propositionalStateFormula, () => propositionalStateFormula);

            CodeWriter.Append("( ");
            propositionalStateFormula.Expression.Accept(this);
            CodeWriter.Append(" )");

        }

        /// <summary>
        ///     Visits an element of type <see cref="BinaryFormula" />.
        /// </summary>
        /// <param name="binaryFormula">The <see cref="BinaryFormula" /> instance that should be visited.</param>
        public override void VisitBinaryFormula(BinaryFormula binaryFormula)
        {
            Argument.NotNull(binaryFormula, () => binaryFormula);

            CodeWriter.Append("( ");
            binaryFormula.Left.Accept(this);

            switch (binaryFormula.Operator)
            {
                case PromelaBinaryFormulaOperator.Equals:
                    CodeWriter.Append(" <-> ");
                    break;
                case PromelaBinaryFormulaOperator.Until:
                    CodeWriter.Append(" U ");
                    break;
                case PromelaBinaryFormulaOperator.WeakUntil:
                    CodeWriter.Append(" W ");
                    break;
                case PromelaBinaryFormulaOperator.Release:
                    CodeWriter.Append(" release ");
                    break;
                case PromelaBinaryFormulaOperator.And:
                    CodeWriter.Append(" /\\ ");
                    break;
                case PromelaBinaryFormulaOperator.Or:
                    CodeWriter.Append(" \\/ ");
                    break;
                case PromelaBinaryFormulaOperator.Implies:
                    CodeWriter.Append(" -> ");
                    break;
                default:
                    throw new ArgumentOutOfRangeException();
            }

            binaryFormula.Right.Accept(this);
            CodeWriter.Append(" )");

        }

        /// <summary>
        ///     Visits an element of type <see cref="UnaryFormula" />.
        /// </summary>
        /// <param name="unaryFormula">The <see cref="UnaryFormula" /> instance that should be visited.</param>
        public override void VisitUnaryFormula(UnaryFormula unaryFormula)
        {
            Argument.NotNull(unaryFormula, () => unaryFormula);
            CodeWriter.Append("( ");

            switch (unaryFormula.Operator)
            {
                case PromelaUnaryFormulaOperator.Not:
                    break;
                case PromelaUnaryFormulaOperator.Always:
                    break;
                case PromelaUnaryFormulaOperator.Eventually:
                    break;
                default:
                    throw new ArgumentOutOfRangeException();
            }

            unaryFormula.Operand.Accept(this);

            CodeWriter.Append(" )");
        }

        #endregion
    }
}