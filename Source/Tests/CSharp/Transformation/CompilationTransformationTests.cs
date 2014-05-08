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
	using SafetySharp.CSharp;
	using SafetySharp.CSharp.Transformation;
	using SafetySharp.Metamodel;
	using SafetySharp.Metamodel.Declarations;
	using SafetySharp.Metamodel.Expressions;
	using SafetySharp.Metamodel.Statements;
	using SafetySharp.Metamodel.Types;

	[TestFixture]
	public class CompilationTransformationTests
	{
		private TestCompilation _compilation;
		private MetamodelCompilation _metamodelCompilation;
		private SymbolMap _symbolMap;

		private void Transform(string csharpCode)
		{
			_compilation = new TestCompilation("using SafetySharp.Modeling; " + csharpCode);
			var transformation = new CompilationTransformation(new ModelingCompilation(_compilation.Compilation));

			_metamodelCompilation = transformation.Transform();
			_symbolMap = transformation.SymbolMap;
		}

		private ComponentDeclaration TransformComponent(string csharpCode)
		{
			Transform(csharpCode);
			return _metamodelCompilation.Components[0];
		}

		private InterfaceDeclaration TransformInterface(string csharpCode)
		{
			Transform(csharpCode);
			return _metamodelCompilation.Interfaces[0];
		}

		private T GetAndCheckSubComponent<T>(MetamodelReference<TypeDeclaration> typeDeclaration)
			where T : TypeDeclaration
		{
			var component = _metamodelCompilation.Resolver.Resolve(typeDeclaration);
			component.Should().BeOfType<T>();
			return (T)component;
		}

		[Test]
		public void ShouldNotTransformSubComponents()
		{
			var component = TransformComponent("class MyComponent : Component { private bool value; }");
			component.SubComponents.Should().HaveCount(0);
		}

		[Test]
		public void ShouldTransformComponentInterface()
		{
			var componentInterface = TransformInterface("interface IMyComponent : IComponent { }");
			componentInterface.Identifier.Name.Should().Be("IMyComponent");
		}

		[Test]
		public void ShouldTransformMethodsWithParameters()
		{
			var component = TransformComponent("class X : Component { bool M() { return true; } void N(int i, bool b) { return; } }");
			component.UpdateMethod.Should().Be(MethodDeclaration.UpdateMethod);

			component.Methods.Should().HaveCount(2);
			component.Methods[0].Identifier.Name.Should().Be("M");
			component.Methods[0].Body.Should().Be(ReturnStatement.ReturnTrue.AsBlockStatement());
			component.Methods[0].ReturnType.Should().Be(TypeSymbol.Boolean);
			component.Methods[0].Parameters.Should().BeEmpty();

			component.Methods[1].Identifier.Name.Should().Be("N");
			component.Methods[1].Body.Should().Be(ReturnStatement.ReturnVoid.AsBlockStatement());
			component.Methods[1].ReturnType.Should().Be(TypeSymbol.Void);
			component.Methods[1].Parameters.Should().HaveCount(2);

			component.Methods[1].Parameters[0].Identifier.Name.Should().Be("i");
			component.Methods[1].Parameters[0].Type.Should().Be(TypeSymbol.Integer);
			component.Methods[1].Parameters[1].Identifier.Name.Should().Be("b");
			component.Methods[1].Parameters[1].Type.Should().Be(TypeSymbol.Boolean);
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
			var component = TransformComponent("class X : Component { public bool Method() { return false; } }");
			component.UpdateMethod.Body.Should().Be(BlockStatement.Empty);
			component.Methods.Length.Should().Be(1);
			component.Methods[0].Identifier.Name.Should().Be("Method");
			component.Methods[0].Body.Should().Be(ReturnStatement.ReturnFalse.AsBlockStatement());
			component.Methods[0].ReturnType.Should().Be(TypeSymbol.Boolean);
			component.Methods[0].Parameters.Should().BeEmpty();
		}

		[Test]
		public void ShouldTransformOneComponentWithoutAnyMembers()
		{
			Transform("class MyComponent : Component {}");
			_metamodelCompilation.Components.Length.Should().Be(1);

			var component = _metamodelCompilation.Components[0];
			component.Methods.Should().BeEmpty();
			component.Fields.Should().BeEmpty();
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
		public void ShouldTransformTwoSubComponents_OfMixedTypes()
		{
			var component = TransformComponent("class MyComponent : Component { private Component c1; private IComponent c2; }");

			component.SubComponents.Should().HaveCount(2);
			component.SubComponents[0].Identifier.Name.Should().Be("c1");
			component.SubComponents[1].Identifier.Name.Should().Be("c2");

			GetAndCheckSubComponent<ComponentDeclaration>(component.SubComponents[0].Type);
			GetAndCheckSubComponent<InterfaceDeclaration>(component.SubComponents[1].Type);
		}

		[Test]
		public void ShouldTransformTwoSubComponents_OfTypeComponent()
		{
			var component = TransformComponent("class MyComponent : Component { private Component c1; private Component c2; }");

			component.SubComponents.Should().HaveCount(2);
			component.SubComponents[0].Identifier.Name.Should().Be("c1");
			component.SubComponents[1].Identifier.Name.Should().Be("c2");

			GetAndCheckSubComponent<ComponentDeclaration>(component.SubComponents[0].Type);
			GetAndCheckSubComponent<ComponentDeclaration>(component.SubComponents[1].Type);
		}

		[Test]
		public void ShouldTransformTwoSubComponents_OfTypeDerivedComponent()
		{
			var component = TransformComponent("class MyComponent : Component { private X c; } class X : Component {}");

			component.SubComponents.Should().HaveCount(1);
			component.SubComponents[0].Identifier.Name.Should().Be("c");

			var subComponent = GetAndCheckSubComponent<ComponentDeclaration>(component.SubComponents[0].Type);
			subComponent.Should().Be(_metamodelCompilation.Components[1]);
		}

		[Test]
		public void ShouldTransformTwoSubComponents_OfTypeDerivedIComponent()
		{
			var component = TransformComponent("class MyComponent : Component { private IX c; } interface IX : IComponent {}");

			component.SubComponents.Should().HaveCount(1);
			component.SubComponents[0].Identifier.Name.Should().Be("c");

			var subComponent = GetAndCheckSubComponent<InterfaceDeclaration>(component.SubComponents[0].Type);
			subComponent.Should().Be(_metamodelCompilation.Interfaces[0]);
		}

		[Test]
		public void ShouldTransformTwoSubComponents_OfTypeIComponent()
		{
			var component = TransformComponent("class MyComponent : Component { private IComponent c1; private IComponent c2; }");

			component.SubComponents.Should().HaveCount(2);
			component.SubComponents[0].Identifier.Name.Should().Be("c1");
			component.SubComponents[1].Identifier.Name.Should().Be("c2");

			GetAndCheckSubComponent<InterfaceDeclaration>(component.SubComponents[0].Type);
			GetAndCheckSubComponent<InterfaceDeclaration>(component.SubComponents[1].Type);
		}

		[Test]
		public void ShouldTransformUpdateMethod()
		{
			var component = TransformComponent("class X : Component { protected override void Update() { return; } }");
			component.UpdateMethod.Body.Should().Be(ReturnStatement.ReturnVoid.AsBlockStatement());
			component.UpdateMethod.Identifier.Name.Should().Be("Update");
			component.UpdateMethod.ReturnType.Should().Be(TypeSymbol.Void);
			component.UpdateMethod.Parameters.Should().BeEmpty();

			component.Methods.Should().BeEmpty();
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
			var updateMethod = MethodDeclaration.UpdateMethod.WithBody(updateBody.AsBlockStatement());

			var expected = new ComponentDeclaration(new Identifier("BooleanComponent"),
													updateMethod,
													ImmutableArray<MethodDeclaration>.Empty,
													ImmutableArray.Create(field),
													ImmutableArray<SubComponentDeclaration>.Empty);

			actual.Should().Be(expected);
		}
	}
}