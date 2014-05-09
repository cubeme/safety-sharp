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

	namespace CompilationTransformationTests
	{
		using System.Collections.Immutable;
		using FluentAssertions;
		using NUnit.Framework;
		using SafetySharp.CSharp.Transformation;
		using SafetySharp.Metamodel;
		using SafetySharp.Metamodel.Declarations;
		using SafetySharp.Metamodel.Expressions;
		using SafetySharp.Metamodel.Statements;
		using SafetySharp.Metamodel.Types;

		internal class CompilationTransformationTests
		{
			private TestCompilation _compilation;
			private MetamodelCompilation _metamodelCompilation;
			private SymbolMap _symbolMap;

			protected MetamodelCompilation TransformCode(string csharpCode)
			{
				_compilation = new TestCompilation(csharpCode);
				var transformation = new CompilationTransformation(_compilation.ModelingCompilation);

				_metamodelCompilation = transformation.Transform();
				_symbolMap = transformation.SymbolMap;

				return _metamodelCompilation;
			}

			protected ComponentDeclaration Transform(string csharpCode)
			{
				return TransformCode(csharpCode).Components[0];
			}

			protected IMetamodelReference<ComponentDeclaration> GetComponentReference(string className)
			{
				var componentSymbol = _compilation.FindClassSymbol(className);
				return _symbolMap.GetComponentReference(componentSymbol);
			}

			protected IMetamodelReference<InterfaceDeclaration> GetInterfaceReference(string interfaceName)
			{
				var interfaceSymbol = _compilation.FindInterfaceSymbol(interfaceName);
				return _symbolMap.GetInterfaceReference(interfaceSymbol);
			}

			protected IMetamodelReference<FieldDeclaration> GetFieldReference(string className, string fieldName)
			{
				var fieldSymbol = _compilation.FindFieldSymbol(className, fieldName);
				return _symbolMap.GetFieldReference(fieldSymbol);
			}
		}

		[TestFixture]
		internal class TransformComponentInterfaces : CompilationTransformationTests
		{
			private ImmutableArray<InterfaceDeclaration> TransformAllInterfaces(string csharpCode)
			{
				return TransformCode(csharpCode).Interfaces;
			}

			[Test]
			public void MultipleEmptyComponentInterface()
			{
				TransformAllInterfaces("interface IMyComponent1 : IComponent { } interface IMyComponent2 : IComponent { }")
					.Should().BeEquivalentTo(
						new InterfaceDeclaration(new Identifier("IMyComponent1")),
						new InterfaceDeclaration(new Identifier("IMyComponent2")));
			}

			[Test]
			public void SingleEmptyComponentInterface()
			{
				TransformAllInterfaces("interface IMyComponent : IComponent { }")
					.Should().BeEquivalentTo(new InterfaceDeclaration(new Identifier("IMyComponent")));
			}
		}

		[TestFixture]
		internal class TransformComponents : CompilationTransformationTests
		{
			private ImmutableArray<ComponentDeclaration> TransformAllComponents(string csharpCode)
			{
				return TransformCode(csharpCode).Components;
			}

			[Test]
			public void EmptyComponent()
			{
				TransformAllComponents("class MyComponent : Component { }")
					.Should().BeEquivalentTo(ComponentDeclaration.Empty.WithIdentifier(new Identifier("MyComponent")));

				TransformAllComponents("namespace X.Y.Z { class MyComponent : Component { }}")
					.Should().BeEquivalentTo(ComponentDeclaration.Empty.WithIdentifier(new Identifier("X.Y.Z.MyComponent")));
			}

			[Test]
			public void NondeterministicBooleanComponent()
			{
				var actual = Transform(@"
					class BooleanComponent : Component
					{
						private bool _value;

						protected override void Update()
						{
							Choose(out _value, true, false);
						}
					}");

				var fieldReference = GetFieldReference("BooleanComponent", "_value");
				var field = new FieldDeclaration(new Identifier("_value"), TypeSymbol.Boolean);

				var assignment1 = new AssignmentStatement(new FieldAccessExpression(fieldReference), BooleanLiteral.True);
				var assignment2 = new AssignmentStatement(new FieldAccessExpression(fieldReference), BooleanLiteral.False);

				var clause1 = new GuardedCommandClause(BooleanLiteral.True, assignment1);
				var clause2 = new GuardedCommandClause(BooleanLiteral.True, assignment2);

				var updateBody = new GuardedCommandStatement(ImmutableArray.Create(clause1, clause2));
				var updateMethod = MethodDeclaration.UpdateMethod.WithBody(updateBody.AsBlockStatement());

				var expected = ComponentDeclaration
					.Empty
					.WithIdentifier(new Identifier("BooleanComponent"))
					.WithUpdateMethod(updateMethod)
					.WithFields(ImmutableArray.Create(field));

				actual.Should().Be(expected);
			}
		}

		[TestFixture]
		internal class TransformMethods : CompilationTransformationTests
		{
			[Test]
			public void MultipleNonUpdateMethods()
			{
				var component = Transform("class X : Component { bool M() { return true; } void N(int i, bool b) { return; } }");
				component.UpdateMethod.Should().Be(MethodDeclaration.UpdateMethod);

				var methodM = new MethodDeclaration(new Identifier("M"),
													TypeSymbol.Boolean,
													ImmutableArray<ParameterDeclaration>.Empty,
													ReturnStatement.ReturnTrue.AsBlockStatement());

				var methodN = new MethodDeclaration(new Identifier("N"),
													TypeSymbol.Void,
													ImmutableArray.Create(new ParameterDeclaration(new Identifier("i"), TypeSymbol.Integer),
																		  new ParameterDeclaration(new Identifier("b"), TypeSymbol.Boolean)),
													ReturnStatement.ReturnVoid.AsBlockStatement());

				component.Methods.Should().BeEquivalentTo(methodM, methodN);
			}

			[Test]
			public void UpdateMethod()
			{
				var component = Transform("class X : Component { protected override void Update() { ; } }");

				component.UpdateMethod.Should().Be(MethodDeclaration.UpdateMethod.WithBody(EmptyStatement.Default.AsBlockStatement()));
				component.Methods.Should().BeEmpty();
			}

			[Test]
			public void UpdateMethodAndOtherMethods()
			{
				var component = Transform("class X : Component { protected override void Update() { ; } public void M() {} }");

				component.UpdateMethod.Should().Be(MethodDeclaration.UpdateMethod.WithBody(EmptyStatement.Default.AsBlockStatement()));
				component.Methods.Should().BeEquivalentTo(
					new MethodDeclaration(new Identifier("M"), TypeSymbol.Void, ImmutableArray<ParameterDeclaration>.Empty, BlockStatement.Empty));
			}
		}

		[TestFixture]
		internal class TransformSubComponents : CompilationTransformationTests
		{
			[Test]
			public void IgnoreNonComponentFields()
			{
				var component = Transform("class MyComponent : Component { bool value; }");
				component.SubComponents.Should().BeEmpty();
			}

			[Test]
			public void MixedInterfaceAndClassSubComponents()
			{
				var component = Transform(@"
					class MyComponent : Component { SubComponent1 c1; SubComponent2 c2; ISubComponent1 c3; ISubComponent2 c4; }
					class SubComponent1 : Component {} 
					class SubComponent2 : Component {}
					interface ISubComponent1 : IComponent {} 
					interface ISubComponent2 : IComponent {}");

				component.SubComponents.Should().BeEquivalentTo(
					new SubComponentDeclaration(new Identifier("c1"), GetComponentReference("SubComponent1")),
					new SubComponentDeclaration(new Identifier("c2"), GetComponentReference("SubComponent2")),
					new SubComponentDeclaration(new Identifier("c3"), GetInterfaceReference("ISubComponent1")),
					new SubComponentDeclaration(new Identifier("c4"), GetInterfaceReference("ISubComponent2")));
			}

			[Test]
			public void RecursiveSubComponentType()
			{
				var component = Transform("class MyComponent : Component { MyComponent c; }");

				component.SubComponents.Should().BeEquivalentTo(
					new SubComponentDeclaration(new Identifier("c"), GetComponentReference("MyComponent")));
			}

			[Test]
			public void SingleSubComponent()
			{
				var component = Transform("class MyComponent : Component { SubComponent c; } class SubComponent : Component {}");
				component.SubComponents.Should().BeEquivalentTo(
					new SubComponentDeclaration(new Identifier("c"), GetComponentReference("SubComponent")));

				component = Transform("interface ISubComponent : IComponent {} class MyComponent : Component { ISubComponent c; }");
				component.SubComponents.Should().BeEquivalentTo(
					new SubComponentDeclaration(new Identifier("c"), GetInterfaceReference("ISubComponent")));
			}
		}

		[TestFixture]
		internal class TransformFields : CompilationTransformationTests
		{
			[Test]
			public void IgnoreComponentFields()
			{
				var component = Transform(@"
					interface MyInterface : IComponent {} 
					class MyComponent2 : Component {}
					class MyComponent : Component { MyComponent2 c1; MyInterface c2; }");

				component.Fields.Should().BeEmpty();
			}

			[Test]
			public void MultipleFields()
			{
				var component = Transform("class X : Component { bool value; int test; decimal other; }");

				component.Fields.Should().BeEquivalentTo(
					new FieldDeclaration(new Identifier("value"), TypeSymbol.Boolean),
					new FieldDeclaration(new Identifier("test"), TypeSymbol.Integer),
					new FieldDeclaration(new Identifier("other"), TypeSymbol.Decimal));
			}

			[Test]
			public void SingleField()
			{
				var component = Transform("class X : Component { bool value; }");

				component.Fields.Should().BeEquivalentTo(
					new FieldDeclaration(new Identifier("value"), TypeSymbol.Boolean));
			}
		}
	}
}