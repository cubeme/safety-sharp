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
	using System.Linq;
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.CSharp.Transformation;
	using SafetySharp.Metamodel;
	using SafetySharp.Metamodel.Configurations;
	using SafetySharp.Metamodel.Declarations;
	using SafetySharp.Metamodel.Expressions;
	using SafetySharp.Metamodel.Statements;
	using SafetySharp.Metamodel.Types;
	using SafetySharp.Modeling;

	[TestFixture]
	internal class MetamodelTransformationTests
	{
		private MetamodelCompilation _metamodelCompilation;
		private MetamodelConfiguration _metamodelConfiguration;
		//private ComponentResolver _componentResolver;
		private ModelConfiguration _configuration;

		private void Transform(string csharpCode, string configurationName)
		{
			var compilation = new TestCompilation(csharpCode);
			_configuration = (ModelConfiguration)Activator.CreateInstance(compilation.Compile().GetType(configurationName));
			var transformation = new MetamodelTransformation(compilation.ModelingCompilation, _configuration.GetSnapshot());

			transformation.TryTransform(out _metamodelCompilation, out _metamodelConfiguration).Should().BeTrue();
			//_componentResolver = transformation.ComponentResolver;
		}

		//private ComponentConfiguration CreateComponentConfiguration(ComponentSnapshot component)
		//{
		//	return new ComponentConfiguration(
		//		Identifier.Unknown,
		//		_componentResolver.Resolve(component),
		//		ImmutableArray<ValueArray>.Empty,
		//		ImmutableArray<ComponentConfiguration>.Empty);
		//}

		//protected IMetamodelReference<ComponentDeclaration> GetComponentReference(string className)
		//{
		//	var componentSymbol = _compilation.FindClassSymbol(className);
		//	return _symbolMap.GetComponentReference(componentSymbol);
		//}

		//protected IMetamodelReference<InterfaceDeclaration> GetInterfaceReference(string interfaceName)
		//{
		//	var interfaceSymbol = _compilation.FindInterfaceSymbol(interfaceName);
		//	return _symbolMap.GetInterfaceReference(interfaceSymbol);
		//}

		//protected IMetamodelReference<FieldDeclaration> GetFieldReference(string className, string fieldName)
		//{
		//	var fieldSymbol = _compilation.FindFieldSymbol(className, fieldName);
		//	return _symbolMap.GetFieldReference(fieldSymbol);
		//}

		[Test]
		public void ModelOfSimpleNondeterministicBooleanSystem()
		{
			var csharpCode = @"
				class BooleanComponent : Component
				{
					private bool _value;

					public BooleanComponent()
					{
						SetInitialValues(() => _value, true, false);
					}

					protected override void Update()
					{
						Choose(out _value, true, false);
					}
				}
				class BooleanConfiguration : ModelConfiguration
				{
					public BooleanConfiguration()
					{
						AddPartitions(new BooleanComponent());
					}
				}";

			Transform(csharpCode, "BooleanConfiguration");
			//_metamodelConfiguration.Partitions.Should().BeEquivalentTo(
			//	new Partition(CreateComponentConfiguration())
			//	);

			//var fieldReference = GetFieldReference("BooleanComponent", "_value");
			//var field = new FieldDeclaration(new Identifier("_value"), TypeSymbol.Boolean);

			//var assignment1 = new AssignmentStatement(new FieldAccessExpression(fieldReference), BooleanLiteral.True);
			//var assignment2 = new AssignmentStatement(new FieldAccessExpression(fieldReference), BooleanLiteral.False);

			//var clause1 = new GuardedCommandClause(BooleanLiteral.True, assignment1);
			//var clause2 = new GuardedCommandClause(BooleanLiteral.True, assignment2);

			//var updateBody = new GuardedCommandStatement(ImmutableArray.Create(clause1, clause2));
			//var updateMethod = MethodDeclaration.UpdateMethod.WithBody(updateBody.AsBlockStatement());

			//var expected = ComponentDeclaration
			//	.Empty
			//	.WithIdentifier(new Identifier("BooleanComponent"))
			//	.WithUpdateMethod(updateMethod)
			//	.WithFields(ImmutableArray.Create(field));

			//actual.Should().Be(expected);
		}

//		[Test]
//		public void Test2()
//		{
//			var csharpCode = @"
//class X : Component
//{
//	private int _field;		
//
//	public X()
//	{
//		SetInitialValues(() => _field, 1, 2, 3, 4, 5, 6);
//	}
//}
//class Y : Component
//{
//	private X _x = new X();
//}
//class Config : ModelConfiguration
//{
//	public Config()
//	{
//		AddPartitions(new Y(), new X());
//	}
//}
//";
//			Transform(csharpCode, "Config");
//			_configuration.Partitions.Should().HaveCount(2);

//			var componentConfiguration = _configuration.Partitions[1].Component;
//			//componentConfiguration.Type.Should().Be(_componentResolver.Resolve(_components["X"]));
//			componentConfiguration.FieldValues.Should().HaveCount(1);
//			componentConfiguration.FieldValues[0].Values.Should().BeEquivalentTo(1, 2, 3, 4, 5, 6);
//			componentConfiguration.SubComponents.Should().HaveCount(0);

//			componentConfiguration = _configuration.Partitions[0].Component;
//			//componentConfiguration.Type.Should().Be(_componentResolver.Resolve(_components["X"]));
//			componentConfiguration.FieldValues.Should().HaveCount(0);
//			componentConfiguration.SubComponents.Should().HaveCount(1);

//			componentConfiguration = componentConfiguration.SubComponents[0];
//			componentConfiguration.FieldValues.Should().HaveCount(1);
//			componentConfiguration.FieldValues[0].Values.Should().BeEquivalentTo(1, 2, 3, 4, 5, 6);
//			componentConfiguration.SubComponents.Should().HaveCount(0);
//		}

//		[Test]
//		public void Test3()
//		{
//			var csharpCode = @"
//class X : Component, Z
//{
//	private int _field;		
//
//	public X()
//	{
//		SetInitialValues(() => _field, 1, 2, 3, 4, 5, 6);
//	}
//}
//interface Z : IComponent {}
//class Y : Component
//{
//	private Z _x = new X();
//}
//class Config : ModelConfiguration
//{
//	public Config()
//	{
//		AddPartitions(new Y(), new X());
//	}
//}
//";
//			Transform(csharpCode, "Config");
//			_configuration.Partitions.Should().HaveCount(2);

//			var componentConfiguration = _configuration.Partitions[1].Component;
//			//componentConfiguration.Type.Should().Be(_componentResolver.Resolve(_components["X"]));
//			componentConfiguration.FieldValues.Should().HaveCount(1);
//			componentConfiguration.FieldValues[0].Values.Should().BeEquivalentTo(1, 2, 3, 4, 5, 6);
//			componentConfiguration.SubComponents.Should().HaveCount(0);

//			componentConfiguration = _configuration.Partitions[0].Component;
//			//componentConfiguration.Type.Should().Be(_componentResolver.Resolve(_components["X"]));
//			componentConfiguration.FieldValues.Should().HaveCount(0);
//			componentConfiguration.SubComponents.Should().HaveCount(1);

//			componentConfiguration = componentConfiguration.SubComponents[0];
//			componentConfiguration.FieldValues.Should().HaveCount(1);
//			componentConfiguration.FieldValues[0].Values.Should().BeEquivalentTo(1, 2, 3, 4, 5, 6);
//			componentConfiguration.SubComponents.Should().HaveCount(0);

//			_compilation.Interfaces.Should().HaveCount(1);
//			_compilation.Components[1].SubComponents.Should().HaveCount(1);
//			_compilation.Components[1].SubComponents[0].Type.Should().BeOfType<MetamodelReference<InterfaceDeclaration>>();
//		}
	}
}