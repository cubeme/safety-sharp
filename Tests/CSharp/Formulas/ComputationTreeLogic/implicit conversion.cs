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
	using SafetySharp.Runtime.Expressions;

	internal class T14 : FormulaTestObject
	{
		private readonly CtlFormula _f1 = true;
		private readonly CtlFormula _f2 = Ctl.StateExpression(true);
		private readonly CtlFormula _f3 = (CtlFormula)true;
		private CtlFormula F1 { get; } = true;
		private CtlFormula F2 { get; } = (CtlFormula)true;

		protected override void Check()
		{
			var expected = new StateFormula(new BooleanLiteralExpression(true));
			CtlFormula f1 = true;
			var f2 = Ctl.StateExpression(true);
			var f3 = (CtlFormula)true;

			Check(_f1, expected);
			Check(_f2, expected);
			Check(_f3, expected);

			Check(F1, expected);
			Check(F2, expected);

			CheckArgumentConversion(true, expected);
			CheckArgumentConversion((CtlFormula)true, expected);
		}

		private void CheckArgumentConversion(CtlFormula actual, CtlFormula expected)
		{
			Check(actual, expected);
		}
	}
}