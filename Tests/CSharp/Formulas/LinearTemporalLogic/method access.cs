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

	internal class T7 : FormulaTestObject
	{
		protected override void Check()
		{
			var c1 = new C1();
			var c2 = new C2();
			var m = new Model();
			m.AddRootComponents(c1, c2);
			m.Seal();

			{
				var actual = Ltl.StateExpression(0 == c1.M(17) - 2);
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.Equals,
						new IntegerLiteralExpression(0),
						new BinaryExpression(BinaryOperator.Subtract,
							new MethodInvocationExpression(
								m.Metadata.RootComponent.Subcomponents[0].ProvidedPorts[1],
								new ArgumentExpression(new IntegerLiteralExpression(17), RefKind.None)),
							new IntegerLiteralExpression(2))
						));

				Check(actual, expected);
			}

			{
				var actual = c1.F;
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.Equals,
						new MethodInvocationExpression(m.Metadata.RootComponent.Subcomponents[0].ProvidedPorts[2]),
						new MethodInvocationExpression(m.Metadata.RootComponent.Subcomponents[0].ProvidedPorts[3],
							new ArgumentExpression(new IntegerLiteralExpression(1), RefKind.None),
							new ArgumentExpression(new BooleanLiteralExpression(true), RefKind.None))));

				Check(actual, expected);
			}

			{
				var actual = Ltl.StateExpression(c2.M3());
				var expected = new StateFormula(new MethodInvocationExpression(m.Metadata.RootComponent.Subcomponents[1].ProvidedPorts[5]));

				Check(actual, expected);
			}

			{
				var ic = c2;
				var actual = Ltl.StateExpression(ic.M3());
				var expected = new StateFormula(new MethodInvocationExpression(m.Metadata.RootComponent.Subcomponents[1].ProvidedPorts[5]));

				Check(actual, expected);
			}

			{
				var actual = Ltl.StateExpression(c2.M(1) == 1);
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.Equals,
						new MethodInvocationExpression(m.Metadata.RootComponent.Subcomponents[1].ProvidedPorts[4],
							new ArgumentExpression(new IntegerLiteralExpression(1), RefKind.None)),
						new IntegerLiteralExpression(1)));

				Check(actual, expected);
			}
		}

		private interface I : IComponent
		{
			[Provided]
			bool M3();
		}

		private class C1 : Component, I
		{
			public readonly LtlFormula F;

			public C1()
			{
				F = Ltl.StateExpression(M0() == M2(1, true));
			}

			public virtual bool M3()
			{
				return true;
			}

			public int M(int i)
			{
				return i + 3;
			}

			public int M0()
			{
				return 3;
			}

			public int M2(int i, bool b)
			{
				return i + 3;
			}
		}

		private class C2 : C1
		{
			public new int M(int i)
			{
				return i + 3;
			}

			public override bool M3()
			{
				return false;
			}
		}
	}
}