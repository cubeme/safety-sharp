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

namespace SafetySharp.CSharp.Transformation
{
	using System;
	using System.Collections.Immutable;
	using System.Linq;
	using Metamodel;
	using Metamodel.Configurations;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Transforms a <see cref="ModelConfiguration" /> instance into a <see cref="MetamodelConfiguration"/>.
	/// </summary>
	internal class ConfigurationTransformation
	{
		/// <summary>
		///     The <see cref="ComponentResolver" /> that is used to resolve components.
		/// </summary>
		private readonly ComponentResolver _componentResolver;

		/// <summary>
		///     The <see cref="MetamodelResolver" /> that is used to resolve metamodel references.
		/// </summary>
		private readonly MetamodelResolver _metamodelResolver;

		/// <summary>
		///     The <see cref="ModelConfiguration" /> instance that is being transformed.
		/// </summary>
		private readonly ModelConfiguration _modelConfiguration;

		/// <summary>
		///     Initializes a new instance of the <see cref="ConfigurationTransformation" /> type.
		/// </summary>
		/// <param name="modelConfiguration">The model configuration that should be transformed.</param>
		/// <param name="metamodelResolver">The <see cref="MetamodelResolver" /> that should be used to resolve metamodel references.</param>
		/// <param name="componentResolver">The <see cref="ComponentResolver" /> that should be used to resolve components.</param>
		internal ConfigurationTransformation(ModelConfiguration modelConfiguration,
											 MetamodelResolver metamodelResolver,
											 ComponentResolver componentResolver)
		{
			Argument.NotNull(modelConfiguration, () => modelConfiguration);
			Argument.NotNull(metamodelResolver, () => metamodelResolver);
			Argument.NotNull(componentResolver, () => componentResolver);

			_modelConfiguration = modelConfiguration;
			_metamodelResolver = metamodelResolver;
			_componentResolver = componentResolver;
		}

		/// <summary>
		///     Transforms the the <see cref="ModelConfiguration" /> instance passed to the constructor into a
		///     <see cref="MetamodelConfiguration" /> instance.
		/// </summary>
		internal MetamodelConfiguration Transform()
		{
			var partitions = _modelConfiguration.PartitionRoots.Aggregate(
				seed: ImmutableArray<Partition>.Empty,
				func: (current, rootComponent) => current.Add(TransformPartition(rootComponent)));

			return new MetamodelConfiguration(partitions);
		}

		/// <summary>
		///     Transforms the partition represented by the <paramref name="partitionRoot" /> component.
		/// </summary>
		/// <param name="partitionRoot">The partition root component that should be transformed.</param>
		private Partition TransformPartition(Component partitionRoot)
		{
			return new Partition(TransformComponent(partitionRoot));
		}

		/// <summary>
		///     Transforms the <paramref name="component" />.
		/// </summary>
		/// <param name="component">The component that should be transformed.</param>
		private ComponentConfiguration TransformComponent(Component component)
		{
			var identifier = new Identifier(component.Name ?? "<unknown>");
			var componentDeclarationReference = _componentResolver.Resolve(component);

			var componentDeclaration = _metamodelResolver.Resolve(componentDeclarationReference);

			var fieldValues = componentDeclaration.Fields.Aggregate(
				seed: ImmutableArray<InitialFieldValues>.Empty,
				func: (current, field) => current.Add(new InitialFieldValues(component.GetInitialValuesOfField(field.Identifier.Name))));

			var subComponents = componentDeclaration.SubComponents.Aggregate(
				seed: ImmutableArray<ComponentConfiguration>.Empty,
				func: (current, subComponent) => current.Add(TransformComponent(component.GetSubComponent(subComponent.Identifier.Name))));

			return new ComponentConfiguration(identifier, componentDeclarationReference, fieldValues, subComponents);
		}
	}
}