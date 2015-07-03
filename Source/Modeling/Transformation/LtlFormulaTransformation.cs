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

namespace SafetySharp.Transformation
{
	using System;
	using System.Globalization;
	using System.Linq;
	using Analysis;
	using Models;
	using Runtime;
	using Runtime.BoundTree;
	using Runtime.Formulas;
	using Utilities;
	using LtlExpression = Models.ScmVerificationElements.LtlExpr;

	/// <summary>
	///     Transforms a <see cref="Formula" /> instance to a <see cref="LtlExpression" /> instance.
	/// </summary>
	internal class LtlFormulaTransformation : BoundTreeVisitor<LtlExpression>
	{
		/// <summary>
		///     The default instance of the <see cref="LtlFormulaTransformation" /> class.
		/// </summary>
		private static readonly LtlFormulaTransformation _instance = new LtlFormulaTransformation();

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		private LtlFormulaTransformation()
		{
		}

		/// <summary>
		///     Transforms the <paramref name="formula" />.
		/// </summary>
		/// <param name="formula">The formula that should be transformed.</param>
		public static LtlExpression Transform(LtlFormula formula)
		{
			Requires.NotNull(formula, () => formula);
			return _instance.Visit(formula);
		}

		/// <summary>
		///     Visits the <paramref name="node" />.
		/// </summary>
		/// <param name="node">The <see cref="BoundNode" /> instance that should be visited.</param>
		protected override LtlExpression DefaultVisit(BoundNode node)
		{
			throw new NotSupportedException(String.Format("Unexpected expression '{0}' in LTL formula.", node));
		}

		/// <summary>
		///     Visits an element of type <see cref="StateFormula" />.
		/// </summary>
		/// <param name="formula">The <see cref="StateFormula" /> instance that should be visited.</param>
		protected internal override LtlExpression VisitStateFormula(StateFormula formula)
		{
			return Visit(formula.Expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="BinaryFormula" />.
		/// </summary>
		/// <param name="formula">The <see cref="BinaryFormula" /> instance that should be visited.</param>
		protected internal override LtlExpression VisitBinaryFormula(BinaryFormula formula)
		{
			var left = Visit(formula.LeftOperand);
			var right = Visit(formula.RightOperand);

			switch (formula.Operator)
			{
				case BinaryFormulaOperator.And:
					return LtlExpression.NewBExpr(left, Scm.BOp.And, right);
				case BinaryFormulaOperator.Or:
					return LtlExpression.NewBExpr(left, Scm.BOp.Or, right);
				case BinaryFormulaOperator.Implication:
					// TODO: Simplify this once the SCM supports the implication operator
					// for now, we use the following transformation: a -> b <=> !a || b
					return LtlExpression.NewBExpr(LtlExpression.NewUExpr(left, Scm.UOp.Not), Scm.BOp.Or, right);
				case BinaryFormulaOperator.Equivalence:
					// TODO: Simplify this once the SCM supports the equivalence operator
					// for now, we use the following transformation: a <-> b <=> (a && b) || !(a || b)
					return LtlExpression.NewBExpr(
						LtlExpression.NewBExpr(left, Scm.BOp.And, right),
						Scm.BOp.Or,
						LtlExpression.NewUExpr(LtlExpression.NewBExpr(left, Scm.BOp.Or, right), Scm.UOp.Not));
				case BinaryFormulaOperator.Until:
					return LtlExpression.NewLbExpr(left, ScmVerificationElements.LbOp.Until, right);
				default:
					Assert.NotReached("Unsupported binary formula operator.");
					return null;
			}
		}

		/// <summary>
		///     Visits an element of type <see cref="UnaryFormula" />.
		/// </summary>
		/// <param name="formula">The <see cref="UnaryFormula" /> instance that should be visited.</param>
		protected internal override LtlExpression VisitUnaryFormula(UnaryFormula formula)
		{
			var operand = Visit(formula.Operand);

			switch (formula.Operator)
			{
				case UnaryFormulaOperator.Not:
					return LtlExpression.NewUExpr(operand, Scm.UOp.Not);
				case UnaryFormulaOperator.Next:
					return LtlExpression.NewLuExpr(operand, ScmVerificationElements.LuOp.Next);
				case UnaryFormulaOperator.Finally:
					return LtlExpression.NewLuExpr(operand, ScmVerificationElements.LuOp.Eventually);
				case UnaryFormulaOperator.Globally:
					return LtlExpression.NewLuExpr(operand, ScmVerificationElements.LuOp.Globally);
				default:
					Assert.NotReached("Unsupported unary formula operator.");
					return null;
			}
		}

		/// <summary>
		///     Visits an element of type <see cref="BinaryExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="BinaryExpression" /> instance that should be visited.</param>
		protected internal override LtlExpression VisitBinaryExpression(BinaryExpression expression)
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

			return LtlExpression.NewBExpr(left, op, right);
		}

		/// <summary>
		///     Visits an element of type <see cref="BooleanLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="BooleanLiteralExpression" /> instance that should be visited.</param>
		protected internal override LtlExpression VisitBooleanLiteralExpression(BooleanLiteralExpression expression)
		{
			return LtlExpression.NewLiteral(Scm.Val.NewBoolVal(expression.Value));
		}

		/// <summary>
		///     Visits an element of type <see cref="ConditionalExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="ConditionalExpression" /> instance that should be visited.</param>
		protected internal override LtlExpression VisitConditionalExpression(ConditionalExpression expression)
		{
			throw new NotImplementedException("No SCM support for conditional expressions within formulas.");
		}

		/// <summary>
		///     Visits an element of type <see cref="DoubleLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="DoubleLiteralExpression" /> instance that should be visited.</param>
		protected internal override LtlExpression VisitDoubleLiteralExpression(DoubleLiteralExpression expression)
		{
			return LtlExpression.NewLiteral(Scm.Val.NewRealVal(expression.Value));
		}

		/// <summary>
		///     Visits an element of type <see cref="EnumerationLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="EnumerationLiteralExpression" /> instance that should be visited.</param>
		protected internal override LtlExpression VisitEnumerationLiteralExpression(EnumerationLiteralExpression expression)
		{
			return LtlExpression.NewLiteral(Scm.Val.NewIntVal(expression.IntegerValue));
		}

		/// <summary>
		///     Visits an element of type <see cref="FieldExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="FieldExpression" /> instance that should be visited.</param>
		protected internal override LtlExpression VisitFieldExpression(FieldExpression expression)
		{
			var component = (ComponentMetadata)expression.Field.DeclaringObject;

			if (expression.Field.FieldInfo.IsInitOnly)
			{
				var value = expression.Field.FieldInfo.GetValue(component.Component);

				if (expression.Field.Type == typeof(int))
					return LtlExpression.NewLiteral(Scm.Val.NewIntVal((int)value));

				if (expression.Field.Type.IsEnum)
					return LtlExpression.NewLiteral(Scm.Val.NewIntVal(((IConvertible)value).ToInt32(CultureInfo.InvariantCulture)));

				if (expression.Field.Type == typeof(double))
					return LtlExpression.NewLiteral(Scm.Val.NewRealVal((double)value));

				if (expression.Field.Type == typeof(bool))
					return LtlExpression.NewLiteral(Scm.Val.NewBoolVal((bool)value));

				Assert.NotReached("Unsupported field type '{0}'.", expression.Field.Type.FullName);
			}

			return ScmVerificationElements.CreateReadField(component.GetPath().Reverse(), expression.Field.Name);
		}

		/// <summary>
		///     Visits an element of type <see cref="IntegerLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="IntegerLiteralExpression" /> instance that should be visited.</param>
		protected internal override LtlExpression VisitIntegerLiteralExpression(IntegerLiteralExpression expression)
		{
			return LtlExpression.NewLiteral(Scm.Val.NewIntVal(expression.Value));
		}

		/// <summary>
		///     Visits an element of type <see cref="UnaryExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="UnaryExpression" /> instance that should be visited.</param>
		protected internal override LtlExpression VisitUnaryExpression(UnaryExpression expression)
		{
			var operand = Visit(expression.Operand);

			switch (expression.Operator)
			{
				case UnaryOperator.Minus:
					return LtlExpression.NewUExpr(operand, Scm.UOp.Minus);
				case UnaryOperator.Not:
					return LtlExpression.NewUExpr(operand, Scm.UOp.Not);
				default:
					Assert.NotReached("Unsupported unary operator.");
					return null;
			}
		}
	}
}