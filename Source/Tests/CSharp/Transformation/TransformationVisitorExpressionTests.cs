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

namespace Tests.CSharp.Transformation
{
	using System;
	using NUnit.Framework;
	using SafetySharp.Metamodel.Expressions;

	[TestFixture]
	internal class TransformationVisitorExpressionTests : TransformationVisitorTests
	{
		[Test]
		public void BinaryAddExpressions()
		{
			Test(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Add, new IntegerLiteral(1)), "1 + 1");
			Test(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.Add, new DecimalLiteral(17.2m)), "13m + 17.2m");
		}

		[Test]
		public void BinaryDivideExpressions()
		{
			Test(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Divide, new IntegerLiteral(1)), "1 / 1");
			Test(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.Divide, new DecimalLiteral(17.2m)), "13m / 17.2m");
		}

		[Test]
		public void BinaryEqualsExpressions()
		{
			Test(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Equals, new IntegerLiteral(1)), "1 == 1");
			Test(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.Equals, new DecimalLiteral(17.2m)), "13m == 17.2m");
		}

		[Test]
		public void BinaryGreaterThanExpressions()
		{
			Test(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.GreaterThan, new IntegerLiteral(1)), "1 > 1");
			Test(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.GreaterThan, new DecimalLiteral(17.2m)), "13m > 17.2m");
		}

		[Test]
		public void BinaryGreaterThanOrEqualExpressions()
		{
			Test(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.GreaterThanOrEqual, new IntegerLiteral(1)), "1 >= 1");
			Test(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.GreaterThanOrEqual, new DecimalLiteral(17.2m)), "13m >= 17.2m");
		}

		[Test]
		public void BinaryLessThanExpressions()
		{
			Test(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.LessThan, new IntegerLiteral(1)), "1 < 1");
			Test(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.LessThan, new DecimalLiteral(17.2m)), "13m < 17.2m");
		}

		[Test]
		public void BinaryLessThanOrEqualExpressions()
		{
			Test(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.LessThanOrEqual, new IntegerLiteral(1)), "1 <= 1");
			Test(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.LessThanOrEqual, new DecimalLiteral(17.2m)), "13m <= 17.2m");
		}

		[Test]
		public void BinaryLogicalAndExpressions()
		{
			Test(new BinaryExpression(BooleanLiteral.False, BinaryOperator.LogicalAnd, BooleanLiteral.True), "false && true");
			Test(new BinaryExpression(BooleanLiteral.True, BinaryOperator.LogicalAnd, BooleanLiteral.True), "true && true");
		}

		[Test]
		public void BinaryLogicalOrExpressions()
		{
			Test(new BinaryExpression(BooleanLiteral.False, BinaryOperator.LogicalOr, BooleanLiteral.True), "false || true");
			Test(new BinaryExpression(BooleanLiteral.True, BinaryOperator.LogicalOr, BooleanLiteral.True), "true || true");
		}

		[Test]
		public void BinaryModuloExpressions()
		{
			Test(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Modulo, new IntegerLiteral(1)), "1 % 1");
			Test(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.Modulo, new DecimalLiteral(17.2m)), "13m % 17.2m");
		}

		[Test]
		public void BinaryMultiplyExpressions()
		{
			Test(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Multiply, new IntegerLiteral(1)), "1 * 1");
			Test(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.Multiply, new DecimalLiteral(17.2m)), "13m * 17.2m");
		}

		[Test]
		public void BinaryNotEqualsExpressions()
		{
			Test(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.NotEquals, new IntegerLiteral(1)), "1 != 1");
			Test(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.NotEquals, new DecimalLiteral(17.2m)), "13m != 17.2m");
		}

		[Test]
		public void BinarySubtractExpressions()
		{
			Test(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Subtract, new IntegerLiteral(1)), "1 - 1");
			Test(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.Subtract, new DecimalLiteral(17.2m)), "13m - 17.2m");
		}

		[Test]
		public void BooleanLiterals()
		{
			Test(BooleanLiteral.False, "false");
			Test(BooleanLiteral.True, "true");
		}

		[Test]
		public void DecimalLiterals()
		{
			Test(new DecimalLiteral(0m), "0m");
			Test(new DecimalLiteral(10m), "10m");
			Test(new DecimalLiteral(0.5m), "0.5m");
			Test(new DecimalLiteral(17.412m), "17.412m");
		}

		[Test]
		public void IntegerLiterals()
		{
			Test(new IntegerLiteral(0), "0");
			Test(new IntegerLiteral(1), "1");
			Test(new IntegerLiteral(10), "10");
			Test(new IntegerLiteral(41223), "41223");
		}

		[Test]
		public void NestedBinaryExpressions()
		{
			var add = new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Add, new IntegerLiteral(2));
			var multiply = new BinaryExpression(add, BinaryOperator.Multiply, new IntegerLiteral(10));
			Test(multiply, "(1 + 2) * 10");

			multiply = new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Multiply, new IntegerLiteral(10));
			add = new BinaryExpression(multiply, BinaryOperator.Add, new IntegerLiteral(2));
			Test(add, "1 * 10 + 2");

			var left = new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Add, new IntegerLiteral(2));
			var right = new BinaryExpression(new IntegerLiteral(4), BinaryOperator.Add, new IntegerLiteral(5));
			multiply = new BinaryExpression(left, BinaryOperator.Multiply, right);
			Test(multiply, "(1 + 2) * (4 + 5)");
		}

		[Test]
		public void NestedUnaryAndBinaryExpressions()
		{
			var minusOne = new UnaryExpression(new IntegerLiteral(1), UnaryOperator.Minus);
			var plusFive = new UnaryExpression(new IntegerLiteral(5), UnaryOperator.Plus);

			var left = new BinaryExpression(minusOne, BinaryOperator.Add, new IntegerLiteral(2));
			var right = new BinaryExpression(new IntegerLiteral(4), BinaryOperator.Add, plusFive);
			var multiply = new BinaryExpression(new UnaryExpression(left, UnaryOperator.Minus), BinaryOperator.Multiply, right);

			Test(multiply, "-(-1 + 2) * (4 + +5)");
		}

		[Test]
		public void NestedUnaryExpressions()
		{
			Test(new UnaryExpression(new UnaryExpression(new IntegerLiteral(1), UnaryOperator.Plus), UnaryOperator.Minus), "-+1");
			Test(new UnaryExpression(new UnaryExpression(BooleanLiteral.True, UnaryOperator.LogicalNot), UnaryOperator.LogicalNot), "!!true");
		}

		[Test]
		public void UnaryMinusExpressions()
		{
			Test(new UnaryExpression(new DecimalLiteral(0.50m), UnaryOperator.Minus), "-.50m");
			Test(new UnaryExpression(new DecimalLiteral(10m), UnaryOperator.Minus), "-10m");
			Test(new UnaryExpression(new IntegerLiteral(4), UnaryOperator.Minus), "-4");
			Test(new UnaryExpression(new IntegerLiteral(0), UnaryOperator.Minus), "-0");
		}

		[Test]
		public void UnaryNotExpressions()
		{
			Test(new UnaryExpression(BooleanLiteral.True, UnaryOperator.LogicalNot), "!true");
			Test(new UnaryExpression(BooleanLiteral.False, UnaryOperator.LogicalNot), "!false");
		}

		[Test]
		public void UnaryPlusExpressions()
		{
			Test(new UnaryExpression(new DecimalLiteral(0.50m), UnaryOperator.Plus), "+.50m");
			Test(new UnaryExpression(new DecimalLiteral(10m), UnaryOperator.Plus), "+10m");
			Test(new UnaryExpression(new IntegerLiteral(4), UnaryOperator.Plus), "+4");
			Test(new UnaryExpression(new IntegerLiteral(0), UnaryOperator.Plus), "+0");
		}
	}
}