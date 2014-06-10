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
	using Metamodel.Configurations;
	using Metamodel.Declarations;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Maps <see cref="Component" />s to their corresponding <see cref="ComponentDeclaration" />s and
	///     <see cref="ComponentConfiguration" />s.
	/// </summary>
	internal class ComponentResolver
	{
		/// <summary>
		///     The empty resolver that cannot resolve any components.
		/// </summary>
		internal static readonly ComponentResolver Empty = new ComponentResolver
		{
			_declarationMap = ImmutableDictionary<Component, ComponentDeclaration>.Empty,
			_configurationMap = ImmutableDictionary<Component, ComponentConfiguration>.Empty
		};

		/// <summary>
		///     Maps <see cref="Component" />s to <see cref="ComponentConfiguration" />s.
		/// </summary>
		private ImmutableDictionary<Component, ComponentConfiguration> _configurationMap;

		/// <summary>
		///     Maps <see cref="Component" />s to <see cref="ComponentDeclaration" />s.
		/// </summary>
		private ImmutableDictionary<Component, ComponentDeclaration> _declarationMap;

		/// <summary>
		///     Initializes a new instance of the <see cref="ComponentResolver" /> type.
		/// </summary>
		private ComponentResolver()
		{
		}

		/// <summary>
		///     Resolves the <see cref="ComponentDeclaration" /> for <paramref name="component" />.
		/// </summary>
		/// <param name="component">The component that should be resolved.</param>
		public ComponentDeclaration ResolveDeclaration(Component component)
		{
			Requires.NotNull(component, () => component);
			Requires.ArgumentSatisfies(_declarationMap.ContainsKey(component), () => component, "The given component is unknown.");

			return _declarationMap[component];
		}

		/// <summary>
		///     Resolves the <see cref="ComponentConfiguration" /> for <paramref name="component" />.
		/// </summary>
		/// <param name="component">The component that should be resolved.</param>
		public ComponentConfiguration ResolveConfiguration(Component component)
		{
			Requires.NotNull(component, () => component);
			Requires.ArgumentSatisfies(_configurationMap.ContainsKey(component), () => component, "The given component is unknown.");

			return _configurationMap[component];
		}

		/// <summary>
		///     Creates a copy of the <see cref="ComponentResolver" /> that can resolve <paramref name="component" /> to
		///     <paramref name="declaration" />.
		/// </summary>
		/// <param name="component">The component that should be added to the resolver.</param>
		/// <param name="declaration">The component declaration that should be resolved.</param>
		public ComponentResolver With(Component component, ComponentDeclaration declaration)
		{
			Requires.NotNull(component, () => component);
			Requires.NotNull(declaration, () => declaration);
			Requires.ArgumentSatisfies(!_declarationMap.ContainsKey(component), () => declaration,
							   "The given declaration has already been added to the resolver.");

			return new ComponentResolver
			{
				_declarationMap = _declarationMap.Add(component, declaration),
				_configurationMap = _configurationMap
			};
		}

		/// <summary>
		///     Creates a copy of the <see cref="ComponentResolver" /> that can resolve <paramref name="component" /> to
		///     <paramref name="configuration" />.
		/// </summary>
		/// <param name="component">The component that should be added to the resolver.</param>
		/// <param name="configuration">The component configuration that should be resolved.</param>
		public ComponentResolver With(Component component, ComponentConfiguration configuration)
		{
			Requires.NotNull(component, () => component);
			Requires.NotNull(configuration, () => configuration);
			Requires.ArgumentSatisfies(!_configurationMap.ContainsKey(component), () => configuration,
							   "The given configuration has already been added to the resolver.");

			return new ComponentResolver
			{
				_declarationMap = _declarationMap,
				_configurationMap = _configurationMap.Add(component, configuration)
			};
		}
	}
}