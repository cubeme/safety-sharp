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
	using System.Linq;
	using FluentAssertions;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using NUnit.Framework;
	using SafetySharp.CSharp.Extensions;
	using SafetySharp.CSharp.Transformation;
	using SafetySharp.Metamodel;
	using SafetySharp.Metamodel.Declarations;
	using SafetySharp.Metamodel.Expressions;

	[TestFixture]
	internal class ExpressionTransformationTests
	{
		private IMetamodelReference<FieldDeclaration> _fieldReference;

		private MetamodelElement Transform(string csharpCode)
		{
			csharpCode = @"
				class C : Component 
				{
					private bool boolField; 
					private int intField;
					void M()
					{
						var x = " + csharpCode + @";
					}
				}";
			var compilation = new TestCompilation(csharpCode);
			var expression = compilation.SyntaxRoot.DescendantNodes<EqualsValueClauseSyntax>().Single().Value;
			_fieldReference = compilation.SymbolMap.GetFieldReference(compilation.FindFieldSymbol("C", "boolField"));

			var visitor = new ExpressionTransformation(compilation.SemanticModel, compilation.SymbolMap);
			return visitor.Visit(expression);
		}

		[Test]
		public void BinaryAddExpressions()
		{
			Transform("1 + 1").
				Should().Be(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Add, new IntegerLiteral(1)));
			Transform("13m + 17.2m")
				.Should().Be(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.Add, new DecimalLiteral(17.2m)));
		}

		[Test]
		public void BinaryDivideExpressions()
		{
			Transform("1 / 1")
				.Should().Be(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Divide, new IntegerLiteral(1)));
			Transform("13m / 17.2m")
				.Should().Be(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.Divide, new DecimalLiteral(17.2m)));
		}

		[Test]
		public void BinaryEqualsExpressions()
		{
			Transform("1 == 1")
				.Should().Be(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Equals, new IntegerLiteral(1)));
			Transform("13m == 17.2m")
				.Should().Be(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.Equals, new DecimalLiteral(17.2m)));
		}

		[Test]
		public void BinaryGreaterThanExpressions()
		{
			Transform("1 > 1")
				.Should().Be(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.GreaterThan, new IntegerLiteral(1)));
			Transform("13m > 17.2m")
				.Should().Be(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.GreaterThan, new DecimalLiteral(17.2m)));
		}

		[Test]
		public void BinaryGreaterThanOrEqualExpressions()
		{
			Transform("1 >= 1")
				.Should().Be(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.GreaterThanOrEqual, new IntegerLiteral(1)));
			Transform("13m >= 17.2m")
				.Should().Be(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.GreaterThanOrEqual, new DecimalLiteral(17.2m)));
		}

		[Test]
		public void BinaryLessThanExpressions()
		{
			Transform("1 < 1")
				.Should().Be(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.LessThan, new IntegerLiteral(1)));
			Transform("13m < 17.2m")
				.Should().Be(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.LessThan, new DecimalLiteral(17.2m)));
		}

		[Test]
		public void BinaryLessThanOrEqualExpressions()
		{
			Transform("1 <= 1")
				.Should().Be(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.LessThanOrEqual, new IntegerLiteral(1)));
			Transform("13m <= 17.2m")
				.Should().Be(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.LessThanOrEqual, new DecimalLiteral(17.2m)));
		}

		[Test]
		public void BinaryLogicalAndExpressions()
		{
			Transform("false && true")
				.Should().Be(new BinaryExpression(BooleanLiteral.False, BinaryOperator.LogicalAnd, BooleanLiteral.True));
			Transform("true && true")
				.Should().Be(new BinaryExpression(BooleanLiteral.True, BinaryOperator.LogicalAnd, BooleanLiteral.True));
		}

		[Test]
		public void BinaryLogicalOrExpressions()
		{
			Transform("false || true")
				.Should().Be(new BinaryExpression(BooleanLiteral.False, BinaryOperator.LogicalOr, BooleanLiteral.True));
			Transform("true || true")
				.Should().Be(new BinaryExpression(BooleanLiteral.True, BinaryOperator.LogicalOr, BooleanLiteral.True));
		}

		[Test]
		public void BinaryModuloExpressions()
		{
			Transform("1 % 1")
				.Should().Be(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Modulo, new IntegerLiteral(1)));
			Transform("13m % 17.2m")
				.Should().Be(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.Modulo, new DecimalLiteral(17.2m)));
		}

		[Test]
		public void BinaryMultiplyExpressions()
		{
			Transform("1 * 1")
				.Should().Be(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Multiply, new IntegerLiteral(1)));
			Transform("13m * 17.2m")
				.Should().Be(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.Multiply, new DecimalLiteral(17.2m)));
		}

		[Test]
		public void BinaryNotEqualsExpressions()
		{
			Transform("1 != 1")
				.Should().Be(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.NotEquals, new IntegerLiteral(1)));
			Transform("13m != 17.2m")
				.Should().Be(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.NotEquals, new DecimalLiteral(17.2m)));
		}

		[Test]
		public void BinarySubtractExpressions()
		{
			Transform("1 - 1")
				.Should().Be(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Subtract, new IntegerLiteral(1)));
			Transform("13m - 17.2m")
				.Should().Be(new BinaryExpression(new DecimalLiteral(13m), BinaryOperator.Subtract, new DecimalLiteral(17.2m)));
		}

		[Test]
		public void BooleanLiterals()
		{
			Transform("false").Should().Be(BooleanLiteral.False);
			Transform("true").Should().Be(BooleanLiteral.True);
		}

		[Test]
		public void DecimalLiterals()
		{
			Transform("0m").Should().Be(new DecimalLiteral(0m));
			Transform("10m").Should().Be(new DecimalLiteral(10m));
			Transform("0.5m").Should().Be(new DecimalLiteral(0.5m));
			Transform("17.412m").Should().Be(new DecimalLiteral(17.412m));
		}

		[Test]
		public void FieldAccessExpression()
		{
			Transform("boolField").Should().Be(new FieldAccessExpression(_fieldReference));
		}

		[Test]
		public void FieldAccessInBinaryExpression()
		{
			Transform("boolField == false")
				.Should().Be(new BinaryExpression(new FieldAccessExpression(_fieldReference), BinaryOperator.Equals, BooleanLiteral.False));
		}

		[Test]
		public void IntegerLiterals()
		{
			Transform("0").Should().Be(new IntegerLiteral(0));
			Transform("1").Should().Be(new IntegerLiteral(1));
			Transform("10").Should().Be(new IntegerLiteral(10));
			Transform("41223").Should().Be(new IntegerLiteral(41223));
		}

		[Test]
		public void NestedBinaryExpressions()
		{
			var add = new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Add, new IntegerLiteral(2));
			var multiply = new BinaryExpression(add, BinaryOperator.Multiply, new IntegerLiteral(10));
			Transform("(1 + 2) * 10").Should().Be(multiply);

			multiply = new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Multiply, new IntegerLiteral(10));
			add = new BinaryExpression(multiply, BinaryOperator.Add, new IntegerLiteral(2));
			Transform("1 * 10 + 2").Should().Be(add);

			var left = new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Add, new IntegerLiteral(2));
			var right = new BinaryExpression(new IntegerLiteral(4), BinaryOperator.Add, new IntegerLiteral(5));
			multiply = new BinaryExpression(left, BinaryOperator.Multiply, right);
			Transform("(1 + 2) * (4 + 5)").Should().Be(multiply);
		}

		[Test]
		public void NestedUnaryAndBinaryExpressions()
		{
			var minusOne = new UnaryExpression(new IntegerLiteral(1), UnaryOperator.Minus);

			var left = new BinaryExpression(minusOne, BinaryOperator.Add, new IntegerLiteral(2));
			var right = new BinaryExpression(new IntegerLiteral(4), BinaryOperator.Add, new IntegerLiteral(5));
			var multiply = new BinaryExpression(new UnaryExpression(left, UnaryOperator.Minus), BinaryOperator.Multiply, right);

			Transform("-(-1 + 2) * (4 + +5)").Should().Be(multiply);
		}

		[Test]
		public void NestedUnaryExpressions()
		{
			Transform("-+1")
				.Should().Be(new UnaryExpression(new IntegerLiteral(1), UnaryOperator.Minus));
			Transform("!!true")
				.Should().Be(new UnaryExpression(new UnaryExpression(BooleanLiteral.True, UnaryOperator.LogicalNot), UnaryOperator.LogicalNot));
		}

		[Test]
		public void UnaryMinusExpressions()
		{
			Transform("-.50m").Should().Be(new UnaryExpression(new DecimalLiteral(0.50m), UnaryOperator.Minus));
			Transform("-10m").Should().Be(new UnaryExpression(new DecimalLiteral(10m), UnaryOperator.Minus));
			Transform("-4").Should().Be(new UnaryExpression(new IntegerLiteral(4), UnaryOperator.Minus));
			Transform("-0").Should().Be(new UnaryExpression(new IntegerLiteral(0), UnaryOperator.Minus));
		}

		[Test]
		public void UnaryNotExpressions()
		{
			Transform("!true").Should().Be(new UnaryExpression(BooleanLiteral.True, UnaryOperator.LogicalNot));
			Transform("!false").Should().Be(new UnaryExpression(BooleanLiteral.False, UnaryOperator.LogicalNot));
		}

		[Test]
		public void UnaryPlusExpressions()
		{
			Transform("+.50m").Should().Be(new DecimalLiteral(0.50m));
			Transform("+10m").Should().Be(new DecimalLiteral(10m));
			Transform("+4").Should().Be(new IntegerLiteral(4));
			Transform("+0").Should().Be(new IntegerLiteral(0));
		}
	}
}