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

namespace Tests.Formulas.LinearTemporalLogic
{
	using System;
	using SafetySharp.Analysis;
	using SafetySharp.Runtime.BoundTree;
	using SafetySharp.Runtime.Formulas;

	internal class T6 : FormulaTestObject
	{
		protected override void Check()
		{
			var intValue = 7;

			{
				var actual = Ltl.U(intValue < 7, false);
				var expected = new BinaryFormula(
					new StateFormula(new BinaryExpression(BinaryOperator.Less, new IntegerLiteralExpression(7), new IntegerLiteralExpression(7))),
					BinaryFormulaOperator.Until,
					PathQuantifier.None,
					new StateFormula(new BooleanLiteralExpression(false)));

				Check(actual, expected);
			}

			{
				var actual = Ltl.U(Ltl.G(intValue >= 7), false);
				var expected = new BinaryFormula(
					new UnaryFormula(
						new StateFormula(new BinaryExpression(BinaryOperator.GreaterEqual, new IntegerLiteralExpression(7), new IntegerLiteralExpression(7))),
						UnaryFormulaOperator.Globally, PathQuantifier.None),
					BinaryFormulaOperator.Until,
					PathQuantifier.None,
					new StateFormula(new BooleanLiteralExpression(false)));

				Check(actual, expected);
			}

			{
				var actual = Ltl.U(intValue >= 7, Ltl.F(false));
				var expected = new BinaryFormula(
					new StateFormula(new BinaryExpression(BinaryOperator.GreaterEqual, new IntegerLiteralExpression(7), new IntegerLiteralExpression(7))),
					BinaryFormulaOperator.Until,
					PathQuantifier.None,
					new UnaryFormula(new StateFormula(new BooleanLiteralExpression(false)), UnaryFormulaOperator.Finally, PathQuantifier.None));

				Check(actual, expected);
			}

			{
				var actual = Ltl.U(Ltl.G(intValue >= 7), Ltl.F(false));
				var expected = new BinaryFormula(
					new UnaryFormula(
						new StateFormula(new BinaryExpression(BinaryOperator.GreaterEqual, new IntegerLiteralExpression(7), new IntegerLiteralExpression(7))),
						UnaryFormulaOperator.Globally, PathQuantifier.None),
					BinaryFormulaOperator.Until,
					PathQuantifier.None,
					new UnaryFormula(new StateFormula(new BooleanLiteralExpression(false)), UnaryFormulaOperator.Finally, PathQuantifier.None));

				Check(actual, expected);
			}
		}
	}
}