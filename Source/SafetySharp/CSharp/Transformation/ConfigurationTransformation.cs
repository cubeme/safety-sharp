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
	///     Transforms a <see cref="ModelConfiguration" /> instance into a <see cref="MetamodelConfiguration" />.
	/// </summary>
	internal class ConfigurationTransformation
	{
		/// <summary>
		///     The <see cref="ModelConfiguration" /> instance that is being transformed.
		/// </summary>
		private readonly ModelConfigurationSnapshot _modelConfiguration;

		/// <summary>
		///     The <see cref="ComponentResolver" /> that is used to resolve components.
		/// </summary>
		private ComponentResolver _componentResolver;

		/// <summary>
		///     Initializes a new instance of the <see cref="ConfigurationTransformation" /> type.
		/// </summary>
		/// <param name="modelConfiguration">The model configuration that should be transformed.</param>
		internal ConfigurationTransformation(ModelConfigurationSnapshot modelConfiguration)
		{
			Argument.NotNull(modelConfiguration, () => modelConfiguration);
			_modelConfiguration = modelConfiguration;
		}

		/// <summary>
		///     Transforms the the <see cref="ModelConfiguration" /> instance passed to the constructor into a
		///     <see cref="MetamodelConfiguration" /> instance.
		/// </summary>
		/// <param name="componentResolver">The <see cref="ComponentResolver" /> that should be used to resolve components.</param>
		internal MetamodelConfiguration Transform(ref ComponentResolver componentResolver)
		{
			Assert.NotNull(componentResolver, "Argument 'componentResolver' cannot be null.");

			_componentResolver = componentResolver;
			var partitions = _modelConfiguration.PartitionRoots.Select(TransformPartition).ToImmutableArray();
			var configuration = new MetamodelConfiguration(partitions);

			componentResolver = _componentResolver;
			return configuration;
		}

		/// <summary>
		///     Transforms the partition represented by the <paramref name="partitionRoot" /> component.
		/// </summary>
		/// <param name="partitionRoot">The partition root component that should be transformed.</param>
		private Partition TransformPartition(ComponentSnapshot partitionRoot)
		{
			return new Partition(TransformComponent(partitionRoot));
		}

		/// <summary>
		///     Transforms the <paramref name="component" />.
		/// </summary>
		/// <param name="component">The component that should be transformed.</param>
		private ComponentConfiguration TransformComponent(ComponentSnapshot component)
		{
			var identifier = component.Name == null ? Identifier.Unknown : new Identifier(component.Name);
			var componentDeclaration = _componentResolver.ResolveDeclaration(component);

			var fields = componentDeclaration.Fields.Select(field =>
			{
				var values = component.GetInitialValuesOfField(field.Identifier.Name);
				return new { Field = field, Configuration = new FieldConfiguration(values.ToImmutableArray()) };
			}).ToImmutableDictionary(field => field.Field, field => field.Configuration);

			var subComponents = componentDeclaration
				.SubComponents
				.Select(subComponent => TransformComponent(component.GetSubComponent(subComponent.Identifier.Name)))
				.ToImmutableArray();

			var configuration = new ComponentConfiguration(identifier, componentDeclaration, fields, subComponents);
			_componentResolver = _componentResolver.With(component, configuration);

			return configuration;
		}
	}
}