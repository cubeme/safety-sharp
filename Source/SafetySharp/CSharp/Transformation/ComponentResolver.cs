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
	using Metamodel;
	using Metamodel.Declarations;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Resolves component declaration references for <see cref="Component" /> instances.
	/// </summary>
	internal class ComponentResolver
	{
		/// <summary>
		///     The empty resolver that cannot resolve any components.
		/// </summary>
		internal static readonly ComponentResolver Empty = new ComponentResolver
		{
			_map = ImmutableDictionary<Component, MetamodelReference<ComponentDeclaration>>.Empty
		};

		/// <summary>
		///     Maps <see cref="Component" /> instances to <see cref="MetamodelReference{ComponentDeclaration}" /> instances.
		/// </summary>
		private ImmutableDictionary<Component, MetamodelReference<ComponentDeclaration>> _map;

		/// <summary>
		///     Initializes a new instance of the <see cref="ComponentResolver" /> type.
		/// </summary>
		private ComponentResolver()
		{
		}

		/// <summary>
		///     Resolves the <see cref="MetamodelReference{ComponentDeclaration}" /> for the <paramref name="component" />.
		/// </summary>
		/// <param name="component">The component that should be resolved.</param>
		public MetamodelReference<ComponentDeclaration> Resolve(Component component)
		{
			Argument.NotNull(component, () => component);
			Argument.Satisfies(_map.ContainsKey(component), () => component, "The given component is unknown.");

			return _map[component];
		}

		/// <summary>
		///     Creates a copy of the <see cref="ComponentResolver" /> that can resolve <paramref name="component" /> to
		///     <paramref name="reference" />.
		/// </summary>
		/// <param name="component">The component that should be added to the resolver.</param>
		/// <param name="reference">The referenced compnent declaration.</param>
		public ComponentResolver With(Component component, MetamodelReference<ComponentDeclaration> reference)
		{
			Argument.NotNull(component, () => component);
			Argument.NotNull(reference, () => reference);
			Argument.Satisfies(!_map.ContainsKey(component), () => reference,
							   "The given reference has already been added to the resolver.");

			return new ComponentResolver { _map = _map.Add(component, reference) };
		}
	}
}