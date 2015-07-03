// The MIT License (MIT)
// 
// Copyright (c) 20_f4-20_f5, Institute for Software & Systems Engineering
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

namespace Tests.Formulas.LinearTemporalLogic
{
	using System;
	using SafetySharp.Analysis;
	using SafetySharp.Runtime.Formulas;
	using SafetySharp.Runtime.BoundTree;

	internal class T_f4 : FormulaTestObject
	{
		private int _f = 1;
		private bool _g = true;

		protected override void Check()
		{
			{
				var actual = Ltl.StateExpression(_f + _f == 0);
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.Equals,
						new BinaryExpression(BinaryOperator.Add, new IntegerLiteralExpression(_f), new IntegerLiteralExpression(_f)),
						new IntegerLiteralExpression(0)));

				Check(actual, expected);
			}

			{
				var actual = Ltl.StateExpression(_f - _f != 0);
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.NotEquals,
						new BinaryExpression(BinaryOperator.Subtract, new IntegerLiteralExpression(_f), new IntegerLiteralExpression(_f)),
						new IntegerLiteralExpression(0)));

				Check(actual, expected);
			}

			{
				var actual = Ltl.StateExpression(_f / _f > 0);
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.Greater,
						new BinaryExpression(BinaryOperator.Divide, new IntegerLiteralExpression(_f), new IntegerLiteralExpression(_f)),
						new IntegerLiteralExpression(0)));

				Check(actual, expected);
			}

			{
				var actual = Ltl.StateExpression(_f * _f >= 0);
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.GreaterEqual,
						new BinaryExpression(BinaryOperator.Multiply, new IntegerLiteralExpression(_f), new IntegerLiteralExpression(_f)),
						new IntegerLiteralExpression(0)));

				Check(actual, expected);
			}

			{
				var actual = Ltl.StateExpression(_f % _f < 0);
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.Less,
						new BinaryExpression(BinaryOperator.Modulo, new IntegerLiteralExpression(_f), new IntegerLiteralExpression(_f)),
						new IntegerLiteralExpression(0)));

				Check(actual, expected);
			}

			{
				var actual = Ltl.StateExpression(_f % _f <= 0);
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.LessEqual,
						new BinaryExpression(BinaryOperator.Modulo, new IntegerLiteralExpression(_f), new IntegerLiteralExpression(_f)),
						new IntegerLiteralExpression(0)));

				Check(actual, expected);
			}

			{
				var actual = Ltl.StateExpression(_g && true);
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.And,
						new BooleanLiteralExpression(_g), 
						new BooleanLiteralExpression(true)));

				Check(actual, expected);
			}

			{
				var actual = Ltl.StateExpression(_g & true);
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.And,
						new BooleanLiteralExpression(_g), 
						new BooleanLiteralExpression(true)));

				Check(actual, expected);
			}

			{
				var actual = Ltl.StateExpression(_g || true);
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.Or,
						new BooleanLiteralExpression(_g), 
						new BooleanLiteralExpression(true)));

				Check(actual, expected);
			}

			{
				var actual = Ltl.StateExpression(_g | true);
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.Or,
						new BooleanLiteralExpression(_g), 
						new BooleanLiteralExpression(true)));

				Check(actual, expected);
			}
		}
	}
}