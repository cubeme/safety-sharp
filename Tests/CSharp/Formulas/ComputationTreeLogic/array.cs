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

using System;

namespace Tests.Formulas.ComputationTreeLogic
{
	using System;
	using SafetySharp.Analysis;
	using SafetySharp.Modeling;
	using SafetySharp.Modeling.Faults;
	using SafetySharp.Runtime.BoundTree;
	using SafetySharp.Runtime.Formulas;

	internal class T16 : FormulaTestObject
	{
		protected override void Check()
		{
			var i = new int[1];
			i[0] = 33;

			var c = new C[2];
			c[0] = new C();
			c[1] = new C();

			var m = new Model();
			m.AddRootComponents(c);
			m.Seal();

			{
				CtlFormula actual = c[0].F == i[0];
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.Equals,
						new FieldExpression(c[0].Metadata.Fields[0]),
						new IntegerLiteralExpression(33)));

				Check(actual, expected);
			}

			{
				CtlFormula actual = c[0].State == c[1].State;
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.Equals,
						new FieldExpression(c[0].Metadata.StateMachine.StateField),
						new FieldExpression(c[1].Metadata.StateMachine.StateField)));

				Check(actual, expected);
			}

			{
				var actual = Ctl.IsOccurring<C.Failure>(c[1]);
				var expected = new FaultOccurrenceFormula(c[1].Metadata.Faults[0]);

				Check(actual, expected);
			}
		}

		private class C : Component
		{
			public int F;

			public enum States
			{
				A,
				B
			}

			public C()
			{
				InitialState(States.A);
				Transition(States.A, States.B);
			}

			[Transient]
			public class Failure : Fault{}
		}
	}
}