// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
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

namespace SafetySharp.Analysis
{
	using System;
	using Formulas;
	using Models;
	using Runtime;
	using Runtime.Expressions;
	using Utilities;

	/// <summary>
	///     Transforms a <see cref="Formula" /> instance to a <see cref="ScmVerificationElements.LtlExpr" /> instance.
	/// </summary>
	internal class LtlFormulaTransformation : FormulaVisitor<ScmVerificationElements.LtlExpr>
	{
		/// <summary>
		///     Visits an element of type <see cref="StateFormula" />.
		/// </summary>
		/// <param name="stateFormula">The <see cref="StateFormula" /> instance that should be visited.</param>
		protected internal override ScmVerificationElements.LtlExpr VisitStateFormula(StateFormula stateFormula)
		{
			return Visit(stateFormula.Expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="BinaryFormula" />.
		/// </summary>
		/// <param name="binaryFormula">The <see cref="BinaryFormula" /> instance that should be visited.</param>
		protected internal override ScmVerificationElements.LtlExpr VisitBinaryFormula(BinaryFormula binaryFormula)
		{
			var left = Visit(binaryFormula.LeftOperand);
			var right = Visit(binaryFormula.RightOperand);

			switch (binaryFormula.Operator)
			{
				case BinaryFormulaOperator.And:
					return ScmVerificationElements.LtlExpr.NewBExpr(left, Scm.BOp.And, right);
				case BinaryFormulaOperator.Or:
					return ScmVerificationElements.LtlExpr.NewBExpr(left, Scm.BOp.Or, right);
				case BinaryFormulaOperator.Implication:
					// TODO: Simplify this once the SCM supports the implication operator
					// for now, we use the following transformation: a -> b <=> !a || b
					return ScmVerificationElements.LtlExpr.NewBExpr(ScmVerificationElements.LtlExpr.NewUExpr(left, Scm.UOp.Not), Scm.BOp.Or, right);
				case BinaryFormulaOperator.Equivalence:
					// TODO: Simplify this once the SCM supports the equivalence operator
					// for now, we use the following transformation: a <-> b <=> (a && b) || !(a || b)
					return ScmVerificationElements.LtlExpr.NewBExpr(
						ScmVerificationElements.LtlExpr.NewBExpr(left, Scm.BOp.And, right),
						Scm.BOp.Or,
						ScmVerificationElements.LtlExpr.NewUExpr(ScmVerificationElements.LtlExpr.NewBExpr(left, Scm.BOp.Or, right), Scm.UOp.Not));
				case BinaryFormulaOperator.Until:
					return ScmVerificationElements.LtlExpr.NewLbExpr(left, ScmVerificationElements.LbOp.Until, right);
				default:
					Assert.NotReached("Unsupported binary formula operator.");
					return null;
			}
		}

		/// <summary>
		///     Visits an element of type <see cref="UnaryFormula" />.
		/// </summary>
		/// <param name="unaryFormula">The <see cref="UnaryFormula" /> instance that should be visited.</param>
		protected internal override ScmVerificationElements.LtlExpr VisitUnaryFormula(UnaryFormula unaryFormula)
		{
			var operand = Visit(unaryFormula.Operand);

			switch (unaryFormula.Operator)
			{
				case UnaryFormulaOperator.Not:
					return ScmVerificationElements.LtlExpr.NewUExpr(operand, Scm.UOp.Not);
				case UnaryFormulaOperator.Next:
					return ScmVerificationElements.LtlExpr.NewLuExpr(operand, ScmVerificationElements.LuOp.Next);
				case UnaryFormulaOperator.Finally:
					return ScmVerificationElements.LtlExpr.NewLuExpr(operand, ScmVerificationElements.LuOp.Eventually);
				case UnaryFormulaOperator.Globally:
					return ScmVerificationElements.LtlExpr.NewLuExpr(operand, ScmVerificationElements.LuOp.Globally);
				default:
					Assert.NotReached("Unsupported unary formula operator.");
					return null;
			}
		}

		/// <summary>
		///     Visits the <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">The <see cref="Expression" /> instance that should be visited.</param>
		protected override ScmVerificationElements.LtlExpr DefaultVisit(Expression expression)
		{
			throw new NotSupportedException(String.Format("Unsupported expression '{0}'.", expression));
		}

		/// <summary>
		///     Visits an element of type <see cref="BinaryExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="BinaryExpression" /> instance that should be visited.</param>
		protected internal override ScmVerificationElements.LtlExpr VisitBinaryExpression(BinaryExpression expression)
		{
			var left = Visit(expression.LeftOperand);
			var right = Visit(expression.RightOperand);
			Scm.BOp op;

			switch (expression.Operator)
			{
				case BinaryOperator.Add:
					op = Scm.BOp.Add;
					break;
				case BinaryOperator.Subtract:
					op = Scm.BOp.Subtract;
					break;
				case BinaryOperator.Multiply:
					op = Scm.BOp.Multiply;
					break;
				case BinaryOperator.Divide:
					op = Scm.BOp.Divide;
					break;
				case BinaryOperator.Modulo:
					op = Scm.BOp.Modulo;
					break;
				case BinaryOperator.And:
					op = Scm.BOp.And;
					break;
				case BinaryOperator.Or:
					op = Scm.BOp.Or;
					break;
				case BinaryOperator.Equals:
					op = Scm.BOp.Equal;
					break;
				case BinaryOperator.NotEquals:
					op = Scm.BOp.NotEqual;
					break;
				case BinaryOperator.Less:
					op = Scm.BOp.Less;
					break;
				case BinaryOperator.LessEqual:
					op = Scm.BOp.LessEqual;
					break;
				case BinaryOperator.Greater:
					op = Scm.BOp.Greater;
					break;
				case BinaryOperator.GreaterEqual:
					op = Scm.BOp.GreaterEqual;
					break;
				default:
					Assert.NotReached("Unsupported binary operator.");
					return null;
			}

			return ScmVerificationElements.LtlExpr.NewBExpr(left, op, right);
		}

		/// <summary>
		///     Visits an element of type <see cref="BooleanLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="BooleanLiteralExpression" /> instance that should be visited.</param>
		protected internal override ScmVerificationElements.LtlExpr VisitBooleanLiteralExpression(BooleanLiteralExpression expression)
		{
			return ScmVerificationElements.LtlExpr.NewLiteral(Scm.Val.NewBoolVal(expression.Value));
		}

		/// <summary>
		///     Visits an element of type <see cref="ConditionalExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="ConditionalExpression" /> instance that should be visited.</param>
		protected internal override ScmVerificationElements.LtlExpr VisitConditionalExpression(ConditionalExpression expression)
		{
			throw new NotImplementedException("SCM support for conditional expression within formulas is missing.");
		}

		/// <summary>
		///     Visits an element of type <see cref="DoubleLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="DoubleLiteralExpression" /> instance that should be visited.</param>
		protected internal override ScmVerificationElements.LtlExpr VisitDoubleLiteralExpression(DoubleLiteralExpression expression)
		{
			return ScmVerificationElements.LtlExpr.NewLiteral(Scm.Val.NewRealVal(expression.Value));
		}

		/// <summary>
		///     Visits an element of type <see cref="EnumerationLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="EnumerationLiteralExpression" /> instance that should be visited.</param>
		protected internal override ScmVerificationElements.LtlExpr VisitEnumerationLiteralExpression(EnumerationLiteralExpression expression)
		{
			return ScmVerificationElements.LtlExpr.NewLiteral(Scm.Val.NewIntVal(expression.IntegerValue));
		}

		/// <summary>
		///     Visits an element of type <see cref="FieldExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="FieldExpression" /> instance that should be visited.</param>
		protected internal override ScmVerificationElements.LtlExpr VisitFieldExpression(FieldExpression expression)
		{
			var component = (ComponentMetadata)expression.Field.DeclaringObject;
			return ScmVerificationElements.CreateReadField(component.GetPath(), expression.Field.Name);
		}

		/// <summary>
		///     Visits an element of type <see cref="IntegerLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="IntegerLiteralExpression" /> instance that should be visited.</param>
		protected internal override ScmVerificationElements.LtlExpr VisitIntegerLiteralExpression(IntegerLiteralExpression expression)
		{
			return ScmVerificationElements.LtlExpr.NewLiteral(Scm.Val.NewIntVal(expression.Value));
		}

		/// <summary>
		///     Visits an element of type <see cref="UnaryExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="UnaryExpression" /> instance that should be visited.</param>
		protected internal override ScmVerificationElements.LtlExpr VisitUnaryExpression(UnaryExpression expression)
		{
			var operand = Visit(expression.Operand);

			switch (expression.Operator)
			{
				case UnaryOperator.Minus:
					return ScmVerificationElements.LtlExpr.NewUExpr(operand, Scm.UOp.Minus);
				case UnaryOperator.Not:
					return ScmVerificationElements.LtlExpr.NewUExpr(operand, Scm.UOp.Not);
				default:
					Assert.NotReached("Unsupported unary operator.");
					return null;
			}
		}
	}
}