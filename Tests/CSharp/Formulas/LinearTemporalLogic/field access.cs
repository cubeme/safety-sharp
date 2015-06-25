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
	using SafetySharp.Analysis.Formulas;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime.Expressions;

	internal class T2 : FormulaTestObject
	{
		protected override void Check()
		{
			var c1 = new C1();
			var c2 = new C2();
			var m = new Model();
			m.AddRootComponents(c1, c2);
			m.Seal();

			var actual = Ltl.StateExpression(c1.F && +c1.C2.F != -c2.F);
			var expected = new StateFormula(
				new BinaryExpression(BinaryOperator.And,
					new FieldExpression(m.Metadata.RootComponent.Subcomponents[0].Fields[0]),
					new BinaryExpression(BinaryOperator.NotEquals,
						new FieldExpression(m.Metadata.RootComponent.Subcomponents[0].Subcomponents[0].Fields[0]),
						new UnaryExpression(UnaryOperator.Minus, new FieldExpression(m.Metadata.RootComponent.Subcomponents[1].Fields[0])))
					));

			Check(actual, expected);
		}

		private class C1 : Component
		{
			public readonly C2 C2 = new C2();
			public bool F;
		}

		private class C2 : Component
		{
			public int F;
		}
	}
}