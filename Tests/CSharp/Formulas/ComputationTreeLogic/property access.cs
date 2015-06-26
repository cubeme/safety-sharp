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
	using SafetySharp.Modeling;
	using SafetySharp.Runtime.Expressions;

	internal class T8 : FormulaTestObject
	{
		protected override void Check()
		{
			var c1 = new C1();
			var c2 = new C2();
			var m = new Model();
			m.AddRootComponents(c1);
			m.Seal();

			{
				var actual = Ctl.StateExpression(!c1.M == false);
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.Equals,
						new UnaryExpression(UnaryOperator.Not,
							new MethodInvocationExpression(m.Metadata.RootComponent.Subcomponents[0].ProvidedPorts[0])),
						new BooleanLiteralExpression(false)));

				Check(actual, expected);
			}

			{
				var actual = Ctl.StateExpression(c1.M2);
				var expected = new StateFormula(new MethodInvocationExpression(m.Metadata.RootComponent.Subcomponents[0].ProvidedPorts[1]));

				Check(actual, expected);
			}

			{
				var actual = Ctl.StateExpression(c2.M2);
				var expected = new StateFormula(new MethodInvocationExpression(m.Metadata.RootComponent.Subcomponents[0].ProvidedPorts[3]));

				Check(actual, expected);
			}

			{
				var ic = c2;
				var actual = Ctl.StateExpression(ic.M2);
				var expected = new StateFormula(new MethodInvocationExpression(m.Metadata.RootComponent.Subcomponents[0].ProvidedPorts[3]));

				Check(actual, expected);
			}

			{
				var actual = Ctl.StateExpression(c2.M);
				var expected = new StateFormula(new MethodInvocationExpression(m.Metadata.RootComponent.Subcomponents[0].ProvidedPorts[2]));

				Check(actual, expected);
			}
		}

		private interface I : IComponent
		{
			[Provided]
			bool M2 { get; }
		}

		private class C1 : Component, I
		{
			public bool M
			{
				get { return false; }
			}

			public virtual bool M2
			{
				get { return true; }
			}
		}

		private class C2 : C1
		{
			public new bool M
			{
				get { return false; }
			}

			public override bool M2
			{
				get { return false; }
			}
		}
	}
}