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
	using System.Collections.Immutable;
	using System.Reflection;
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.CSharp.Transformation;
	using SafetySharp.Formulas;
	using SafetySharp.Metamodel.Expressions;
	using SafetySharp.Modeling;

	[TestFixture]
	internal class FormulaTransformationTests
	{
		[SetUp]
		public void Setup()
		{
			const string csharpCode = @"
				class X : Component
				{
					public int IntField;
					public bool BooleanField;
				}";

			_compilation = new TestCompilation(csharpCode);
			_assembly = _compilation.Compile();
		}

		private Assembly _assembly;
		private TestCompilation _compilation;

		private StateFormula TransformStateFormula(string csharpExpression, params object[] values)
		{
			var transformation = new FormulaTransformation(_compilation.ModelingCompilation, new SymbolMap(_compilation.CSharpCompilation));

			var untransformed = new UntransformedStateFormula(csharpExpression, values.ToImmutableArray());
			return (StateFormula)transformation.Visit(untransformed);
		}

		private Component CreateComponentInstance(string componentName)
		{
			return (Component)Activator.CreateInstance(_assembly.GetType(componentName));
		}

		[Test]
		public void TransformComponentAccess()
		{
			TransformStateFormula("{0}.BooleanField", CreateComponentInstance("X"))
				.Should().Be(null);
		}

		[Test]
		public void TransformValueAccess()
		{
			TransformStateFormula("{0}", true).Should().Be(new StateFormula(BooleanLiteral.True, null));
			TransformStateFormula("{1} == {0}", 2, 1)
				.Should().Be(new StateFormula(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Equals, new IntegerLiteral(2)), null));
			TransformStateFormula("{0} || {1}", true, false)
				.Should().Be(new StateFormula(new BinaryExpression(BooleanLiteral.True, BinaryOperator.LogicalOr, BooleanLiteral.False), null));
		}

		[Test]
		public void TransformLiteralExpressions()
		{
			TransformStateFormula("true").Should().Be(new StateFormula(BooleanLiteral.True, null));
			TransformStateFormula("1 == 2")
				.Should().Be(new StateFormula(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Equals, new IntegerLiteral(2)), null));
			TransformStateFormula("true || false")
				.Should().Be(new StateFormula(new BinaryExpression(BooleanLiteral.True, BinaryOperator.LogicalOr, BooleanLiteral.False), null));
		}
	}
}