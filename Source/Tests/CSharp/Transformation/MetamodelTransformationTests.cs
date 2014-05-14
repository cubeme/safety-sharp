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
		private ComponentResolver _componentResolver;
		private SymbolMap _symbolMap;
		private ModelConfigurationSnapshot _configuration;
		private TestCompilation _compilation;

		private bool Transform(string csharpCode, string configurationName)
		{
			_compilation = new TestCompilation(csharpCode);
			_configuration = ((ModelConfiguration)Activator.CreateInstance(_compilation.Compile().GetType(configurationName))).GetSnapshot();

			var transformation = new MetamodelTransformation(_compilation.ModelingCompilation, _configuration);
			return transformation.TryTransform(out _metamodelCompilation, out _metamodelConfiguration, out _symbolMap, out _componentResolver);
		}

		private ComponentConfiguration CreateComponentConfiguration(ComponentSnapshot component, string name = null)
		{
			return new ComponentConfiguration(
				name == null ? Identifier.Unknown : new Identifier(name),
				_componentResolver.Resolve(component),
				ImmutableArray<ValueArray>.Empty,
				ImmutableArray<ComponentConfiguration>.Empty);
		}

		private IMetamodelReference<ComponentDeclaration> GetComponentReference(string className)
		{
			var componentSymbol = _compilation.FindClassSymbol(className);
			return _symbolMap.GetComponentReference(componentSymbol);
		}

		private IMetamodelReference<InterfaceDeclaration> GetInterfaceReference(string interfaceName)
		{
			var interfaceSymbol = _compilation.FindInterfaceSymbol(interfaceName);
			return _symbolMap.GetInterfaceReference(interfaceSymbol);
		}

		private IMetamodelReference<FieldDeclaration> GetFieldReference(string className, string fieldName)
		{
			var fieldSymbol = _compilation.FindFieldSymbol(className, fieldName);
			return _symbolMap.GetFieldReference(fieldSymbol);
		}

		private static ImmutableArray<Value> ToValues(params object[] values)
		{
			return values.Select(value => new Value(value)).ToImmutableArray();
		}

		private static ImmutableArray<ValueArray> ToValueArray(params ImmutableArray<Value>[] valueArrays)
		{
			return ImmutableArray.CreateRange(valueArrays.Select(values => new ValueArray(values)));
		}

		[Test]
		public void ModelOfSimpleNondeterministicBooleanSystem()
		{
			const string csharpCode = @"
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

			Transform(csharpCode, "BooleanConfiguration").Should().BeTrue();

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

			_metamodelCompilation.Components.Should().BeEquivalentTo(expected);
			_metamodelCompilation.Interfaces.Should().BeEmpty();

			_metamodelConfiguration.Partitions.Should().BeEquivalentTo(
				new Partition(CreateComponentConfiguration(_configuration.PartitionRoots[0])
								  .WithFieldValues(ToValueArray(ToValues(true, false)))));
		}

		[Test]
		public void ModelWithInterfaceSubComponent()
		{
			const string csharpCode = @"
				interface ITestComponent : IComponent {}
				class X : Component, ITestComponent
				{
				}
				class Y : Component
				{
					private ITestComponent _x = new X();
				}
				class Configuration : ModelConfiguration
				{
					public Configuration()
					{
						AddPartitions(new Y());
					}
				}";

			Transform(csharpCode, "Configuration").Should().BeTrue();

			var componentInterface = new InterfaceDeclaration(new Identifier("ITestComponent"));
			var component1 = ComponentDeclaration.Empty.WithIdentifier(new Identifier("X"));
			var component2 = ComponentDeclaration
				.Empty
				.WithIdentifier(new Identifier("Y"))
				.WithSubComponents(ImmutableArray.Create(
					new SubComponentDeclaration(new Identifier("_x"), GetInterfaceReference("ITestComponent"))));

			_metamodelCompilation.Components.Should().BeEquivalentTo(component1, component2);
			_metamodelCompilation.Interfaces.Should().BeEquivalentTo(componentInterface);

			_metamodelConfiguration.Partitions.Should().BeEquivalentTo(
				new Partition(CreateComponentConfiguration(_configuration.PartitionRoots[0])
								  .WithSubComponents(ImmutableArray.Create(
									  CreateComponentConfiguration(_configuration.PartitionRoots[0].SubComponents[0], "_x")))));
		}

		[Test]
		public void ModelWithNonInterfaceSubComponentsAndTwoPartitions()
		{
			const string csharpCode = @"
				class X : Component
				{
				}
				class Y : Component
				{
					private X _x = new X();
				}
				class Configuration : ModelConfiguration
				{
					public Configuration()
					{
						AddPartitions(new X(), new Y());
					}
				}";

			Transform(csharpCode, "Configuration").Should().BeTrue();

			var component1 = ComponentDeclaration.Empty.WithIdentifier(new Identifier("X"));
			var component2 = ComponentDeclaration
				.Empty
				.WithIdentifier(new Identifier("Y"))
				.WithSubComponents(ImmutableArray.Create(new SubComponentDeclaration(new Identifier("_x"), GetComponentReference("X"))));

			_metamodelCompilation.Components.Should().BeEquivalentTo(component1, component2);
			_metamodelCompilation.Interfaces.Should().BeEmpty();

			_metamodelConfiguration.Partitions.Should().BeEquivalentTo(
				new Partition(CreateComponentConfiguration(_configuration.PartitionRoots[0])),
				new Partition(CreateComponentConfiguration(_configuration.PartitionRoots[1])
								  .WithSubComponents(ImmutableArray.Create(
									  CreateComponentConfiguration(_configuration.PartitionRoots[1].SubComponents[0], "_x")))));
		}
	}
}