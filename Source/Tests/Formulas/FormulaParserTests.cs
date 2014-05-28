// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

namespace Tests.Formulas
{
	using System;
	using FluentAssertions;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using NUnit.Framework;
	using SafetySharp.FSharp.Formulas;

	class T : FormulaVisitor
	{
		public override void VisitBinaryFormula(Formula leftOperand, BinaryOperator @operator, Formula rightOperand)
		{
			Visit(leftOperand);
			Visit(rightOperand);
		}

		public override void VisitExpressionFormula(ExpressionSyntax expression)
		{
			
		}

		public override void VisitUnaryFormula(UnaryOperator @operator, Formula operand)
		{
			Visit(operand);
		}
	}

	[TestFixture]
	internal class FormulaParserTests
	{
		[Test]
		public void Test()
		{
			Formula formula;
			FormulaParser.TryParse("G {v.x == true} || !({true} U {false})", s => { }, out formula).Should().BeTrue();

			var t = new T();
			t.Visit(formula);

			FormulaParser.TryParse("G {v.x == true} || !(true U {false})", Console.WriteLine, out formula).Should().BeFalse();
			FormulaParser.TryParse("G {v.x == true} || !({true} U (X {false}))", Console.WriteLine, out formula).Should().BeFalse();

			Console.WriteLine(formula.ToString());
		}
	}
}