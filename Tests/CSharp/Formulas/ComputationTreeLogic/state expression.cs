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

namespace Tests.Formulas.ComputationTreeLogic
{
	using System;
	using SafetySharp.Analysis;
	using SafetySharp.Analysis.Formulas;
	using SafetySharp.Runtime.BoundTree;

	internal class T1 : FormulaTestObject
	{
		protected override void Check()
		{
			var intValue = 7;
			var enumValue = E.B;

			var expected = new StateFormula(
				new BinaryExpression(BinaryOperator.Or,
					new BinaryExpression(BinaryOperator.Equals, new EnumerationLiteralExpression(E.B), new EnumerationLiteralExpression(E.C)),
					new BinaryExpression(BinaryOperator.Equals,
						new BinaryExpression(BinaryOperator.Greater,
							new BinaryExpression(BinaryOperator.Multiply,
								new BinaryExpression(BinaryOperator.Divide,
									new IntegerLiteralExpression(7),
									new IntegerLiteralExpression(2)),
								new IntegerLiteralExpression(3)),
							new IntegerLiteralExpression(45)),
						new BooleanLiteralExpression(false))
					));

			{
				var actual = Ctl.StateExpression(enumValue == E.C || ((intValue / 2) * 3) > 45 == false);
				Check(actual, expected);
			}

			{
				var actual = (CtlFormula)(enumValue == E.C || ((intValue / 2) * 3) > 45 == false);
				Check(actual, expected);
			}

			{
				// ReSharper disable once JoinDeclarationAndInitializer
				CtlFormula actual;
				actual = enumValue == E.C || ((intValue / 2) * 3) > 45 == false;
				Check(actual, expected);
			}

			{
				CtlFormula actual = enumValue == E.C || ((intValue / 2) * 3) > 45 == false;
				Check(actual, expected);
			}
		}

		private enum E
		{
			A,
			B,
			C
		}
	}
}