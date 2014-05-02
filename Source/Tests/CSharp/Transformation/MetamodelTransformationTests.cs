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
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.CSharp.Transformation;
	using SafetySharp.Metamodel;
	using SafetySharp.Metamodel.Declarations;
	using SafetySharp.Metamodel.Expressions;
	using SafetySharp.Metamodel.Statements;
	using SafetySharp.Metamodel.Types;

	[TestFixture]
	public class MetamodelTransformationTests
	{
		private TestCompilation _compilation;
		private Model _model;
		private SymbolMap _symbolMap;

		private void Transform(string csharpCode)
		{
			_compilation = new TestCompilation("using SafetySharp.Modeling; " + csharpCode);
			var transformation = new MetamodelTransformation();

			_model = transformation.Transform(_compilation.Compilation);
			_symbolMap = transformation.SymbolMap;
		}

		private ComponentDeclaration TransformComponent(string csharpCode)
		{
			Transform(csharpCode);
			return _model.Components[0];
		}

		[Test]
		public void ShouldTransformMultipleFields()
		{
			var component = TransformComponent("class X : Component { private bool value; private int test; private decimal other; }");
			component.Fields.Length.Should().Be(3);

			var field1 = component.Fields[0];
			var field2 = component.Fields[1];
			var field3 = component.Fields[2];

			field1.Identifier.Name.Should().Be("value");
			field2.Identifier.Name.Should().Be("test");
			field3.Identifier.Name.Should().Be("other");

			field1.Type.Should().Be(TypeSymbol.Boolean);
			field2.Type.Should().Be(TypeSymbol.Integer);
			field3.Type.Should().Be(TypeSymbol.Decimal);
		}

		[Test]
		public void ShouldTransformNamespacedComponentName()
		{
			var component = TransformComponent("namespace Tests.Components { class MyComponent : Component {} }");
			component.Identifier.Name.Should().Be("Tests.Components.MyComponent");
		}

		[Test]
		public void ShouldTransformNoUpdateMethodButOtherMethods()
		{
			var component = TransformComponent("class X : Component { public bool M() { return false; } }");
			component.UpdateMethod.Body.Should().Be(BlockStatement.Empty);
			component.Methods.Length.Should().Be(1);
			component.Methods[0].Body.Should().Be(new ReturnStatement(BooleanLiteral.False).AsBlockStatement());
		}

		[Test]
		public void ShouldTransformOneComponentWithoutAnyMembers()
		{
			Transform("class MyComponent : Component {}");
			_model.Components.Length.Should().Be(1);

			var component = _model.Components[0];
			component.Methods.Length.Should().Be(0);
			component.Fields.Length.Should().Be(0);
		}

		[Test]
		public void ShouldTransformSimpleComponentName()
		{
			var component = TransformComponent("class MyComponent : Component {}");
			component.Identifier.Name.Should().Be("MyComponent");
		}

		[Test]
		public void ShouldTransformSingleField()
		{
			var component = TransformComponent("class X : Component { private bool value; }");
			component.Fields.Length.Should().Be(1);

			var field = component.Fields[0];
			field.Identifier.Name.Should().Be("value");
			field.Type.Should().Be(TypeSymbol.Boolean);
		}

		[Test]
		public void ShouldTransformUpdateMethod()
		{
			var component = TransformComponent("class X : Component { protected override void Update() { return; } }");
			component.UpdateMethod.Body.Should().Be(ReturnStatement.ReturnVoid.AsBlockStatement());
			component.Methods.Length.Should().Be(0);
		}

		[Test]
		public void ShouldTransformUpdateMethodAndOtherMethods()
		{
			var component = TransformComponent("class X : Component { protected override void Update() { return; } public void M() {} }");
			component.UpdateMethod.Body.Should().Be(ReturnStatement.ReturnVoid.AsBlockStatement());
			component.Methods.Length.Should().Be(1);
			component.Methods[0].Body.Should().Be(BlockStatement.Empty);
		}

		[Test]
		public void SimpleNondeterministicBooleanComponent()
		{
			var actual = TransformComponent(@"
class BooleanComponent : SafetySharp.Modeling.Component
{
	private bool _value;

	protected override void Update()
	{
		Choose(out _value, true, false);
	}
}");

			var fieldSymbol = _compilation.FindFieldSymbol("BooleanComponent", "_value");
			var fieldReference = _symbolMap.GetFieldReference(fieldSymbol);
			var field = new FieldDeclaration(new Identifier("_value"), TypeSymbol.Boolean);

			var assignment1 = new AssignmentStatement(new FieldAccessExpression(fieldReference), BooleanLiteral.True);
			var assignment2 = new AssignmentStatement(new FieldAccessExpression(fieldReference), BooleanLiteral.False);

			var clause1 = new GuardedCommandClause(BooleanLiteral.True, assignment1);
			var clause2 = new GuardedCommandClause(BooleanLiteral.True, assignment2);

			var updateBody = new GuardedCommandStatement(ImmutableArray.Create(clause1, clause2));
			var updateMethod = new MethodDeclaration(new Identifier("Update"), updateBody.AsBlockStatement());

			var expected = new ComponentDeclaration(new Identifier("BooleanComponent"),
													updateMethod,
													ImmutableArray<MethodDeclaration>.Empty,
													ImmutableArray.Create(field));

			actual.Should().Be(expected);
		}
	}
}