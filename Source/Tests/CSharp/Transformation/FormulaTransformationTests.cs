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
	using SafetySharp.Metamodel;
	using SafetySharp.Metamodel.Declarations;
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

			_symbolMap = new SymbolMap(_compilation.CSharpCompilation);
			_intFieldReference = _symbolMap.GetFieldReference(_compilation.FindFieldSymbol("X", "IntField"));
			_booleanFieldReference = _symbolMap.GetFieldReference(_compilation.FindFieldSymbol("X", "BooleanField"));
		}

		private SymbolMap _symbolMap;
		private Assembly _assembly;
		private TestCompilation _compilation;
		private IMetamodelReference<FieldDeclaration> _intFieldReference;
		private IMetamodelReference<FieldDeclaration> _booleanFieldReference;

		private Formula Transform(Formula formula)
		{
			var transformation = new FormulaTransformation(_compilation.ModelingCompilation, _symbolMap);
			return transformation.Visit(formula);
		}

		private StateFormula TransformStateFormula(string csharpExpression, params object[] values)
		{
			var transformation = new FormulaTransformation(_compilation.ModelingCompilation, _symbolMap);

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
			var component1 = CreateComponentInstance("X");
			var component2 = CreateComponentInstance("X");
			var fieldAccess = new FieldAccessExpression(_booleanFieldReference);

			TransformStateFormula("{0}.BooleanField", component1)
				.Should().Be(new StateFormula(fieldAccess, null));

			TransformStateFormula("{0}.BooleanField == {1}.BooleanField", component1, component1)
				.Should().Be(new StateFormula(new BinaryExpression(fieldAccess, BinaryOperator.Equals, fieldAccess), null));

			TransformStateFormula("{0}.BooleanField == {1}.BooleanField", component1, component2)
				.Should().Be(new StateFormula(new BinaryExpression(fieldAccess, BinaryOperator.Equals, fieldAccess), null));
		}

		[Test]
		public void TransformInternalAccess()
		{
			var fieldAccess = new FieldAccessExpression(_intFieldReference);
			TransformStateFormula("{0} == 2", CreateComponentInstance("X").AccessInternal<int>("IntField"))
				.Should().Be(new StateFormula(new BinaryExpression(fieldAccess, BinaryOperator.Equals, new IntegerLiteral(2)), null));
		}

		[Test]
		public void TransformLiteralExpressions()
		{
			TransformStateFormula("true").Should().Be(new StateFormula(BooleanLiteral.True, null));
			TransformStateFormula("1 == 2")
				.Should().Be(new StateFormula(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Equals, new IntegerLiteral(2)), null));
			TransformStateFormula("1m == 2.5m")
				.Should().Be(new StateFormula(new BinaryExpression(new DecimalLiteral(1), BinaryOperator.Equals, new DecimalLiteral(2.5m)), null));
			TransformStateFormula("true || false")
				.Should().Be(new StateFormula(new BinaryExpression(BooleanLiteral.True, BinaryOperator.LogicalOr, BooleanLiteral.False), null));
		}

		[Test]
		public void TransformNestedFormula()
		{
			var booleanFieldAccess = new FieldAccessExpression(_booleanFieldReference);
			var intFieldAccess = new FieldAccessExpression(_intFieldReference);

			var fieldIsTrue = new UntransformedStateFormula("{0}.BooleanField", ImmutableArray.Create<object>(CreateComponentInstance("X")));
			var fieldIsTwo = new UntransformedStateFormula("{0}.IntField == 2", ImmutableArray.Create<object>(CreateComponentInstance("X")));

			var transformedFieldIsTrue = new StateFormula(booleanFieldAccess, null);
			var transformedfieldIsTwo = new StateFormula(new BinaryExpression(intFieldAccess, BinaryOperator.Equals, new IntegerLiteral(2)), null);

			Transform(new BinaryFormula(fieldIsTrue, BinaryTemporalOperator.Until, PathQuantifier.All, fieldIsTwo)).Should().Be(
				new BinaryFormula(transformedFieldIsTrue, BinaryTemporalOperator.Until, PathQuantifier.All, transformedfieldIsTwo));
		}

		[Test]
		public void TransformValueAccess()
		{
			TransformStateFormula("{0}", true).Should().Be(new StateFormula(BooleanLiteral.True, null));
			TransformStateFormula("{1} == {0}", 2, 1)
				.Should().Be(new StateFormula(new BinaryExpression(new IntegerLiteral(1), BinaryOperator.Equals, new IntegerLiteral(2)), null));
			TransformStateFormula("{1} == {0}", 2m, 1.5m)
				.Should().Be(new StateFormula(new BinaryExpression(new DecimalLiteral(1.5m), BinaryOperator.Equals, new DecimalLiteral(2)), null));
			TransformStateFormula("{0} || {1}", true, false)
				.Should().Be(new StateFormula(new BinaryExpression(BooleanLiteral.True, BinaryOperator.LogicalOr, BooleanLiteral.False), null));
		}
	}
}