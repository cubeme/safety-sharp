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

	internal class T7 : FormulaTestObject
	{
		protected override void Check()
		{
			var c = new C();
			var m = new Model();
			m.AddRootComponents(c);
			m.Seal();

			{
				var actual = Ctl.StateExpression(0 == c.M(17) - 2);
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.Equals,
						new IntegerLiteralExpression(0),
						new BinaryExpression(BinaryOperator.Subtract,
							new MethodInvocationExpression(
								m.Metadata.RootComponent.Subcomponents[0].ProvidedPorts[0],
								new ArgumentExpression(new IntegerLiteralExpression(17), RefKind.None)),
							new IntegerLiteralExpression(2))
						));

				Check(actual, expected);
			}

			{
				var actual = c.F;
				var expected = new StateFormula(
					new BinaryExpression(BinaryOperator.Equals,
						new MethodInvocationExpression(m.Metadata.RootComponent.Subcomponents[0].ProvidedPorts[1]),
						new MethodInvocationExpression(m.Metadata.RootComponent.Subcomponents[0].ProvidedPorts[2],
							new ArgumentExpression(new IntegerLiteralExpression(1), RefKind.None),
							new ArgumentExpression(new BooleanLiteralExpression(true), RefKind.None))));

				Check(actual, expected);
			}
		}

		private class C : Component
		{
			public readonly CtlFormula F;

			public C()
			{
				F = Ctl.StateExpression(M0() == M2(1, true));
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
	}
}