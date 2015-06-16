// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
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

namespace SafetySharp.Modeling
{
	using System;
	using System.Collections.Generic;
	using System.Diagnostics;
	using System.Linq;
	using System.Reflection;
	using Utilities;

	partial class Component
	{
		/// The name of the synthesized root component.
		internal const string SynthesizedRootName = "R";

		/// <summary>
		///     The name of the component.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private string _name = String.Empty;

		/// <summary>
		///     The component's parent component. <c>null</c> for the root of the hierarchy.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private Component _parent;

		/// <summary>
		///     The field of the parent component the component is stored in. <c>null</c> for root components.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private FieldInfo _parentField;

		/// <summary>
		///     The slot of the component, i.e., the zero-based index in the parent component's subcomponent list.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private int _slot;

		/// <summary>
		///     The list of subcomponents.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private List<Component> _subcomponents;

		/// <summary>
		///     Gets the unique name of the component instance. Returns the empty string if no component name could be determined.
		/// </summary>
		internal string Name
		{
			get
			{
				RequiresIsSealed();

				var name = _parent != null ? String.Format("{0}.{1}", _parent.Name, _name) : _name;
				if (_slot == -1)
					return name;

				return String.Format("{0}@{1}", name, _slot);
			}
		}

		/// <summary>
		///     Gets the unmangled, non-unique name of the component instance. Returns the empty string if no component name could be
		///     determined.
		/// </summary>
		internal string UnmangledName
		{
			get
			{
				RequiresIsSealed();

				if (_parent != null)
					return String.Format("{0}.{1}", _parent.UnmangledName, _name);

				return _name.Substring(SynthesizedRootName.Length + 1);
			}
		}

		/// <summary>
		///     Gets the <see cref="Component" /> instances that are direct subcomponents of the current instance.
		/// </summary>
		internal List<Component> Subcomponents
		{
			get
			{
				RequiresIsSealed();
				return _subcomponents;
			}
		}

		/// <summary>
		///     Gets the parent component of the component within the hierarchy or null if the component represents the root of the
		///     hierarchy.
		/// </summary>
		internal Component Parent
		{
			get
			{
				RequiresIsSealed();
				return _parent;
			}
		}

		/// <summary>
		///     Gets the field of the parent component the component is stored in. Returns null for root components.
		/// </summary>
		internal FieldInfo ParentField
		{
			get
			{
				RequiresIsSealed();
				return _parentField;
			}
		}

		/// <summary>
		///     Initializes the subcomponents of the components.
		/// </summary>
		private void InitializeSubcomponents()
		{
			// We skip that step when the subcomponents have already been provided via the constructor (namely: for the synthesized root component)
			if (_subcomponents != null)
				return;

			var subcomponentMetadata = GetType()
				.GetFields(typeof(Component))
				.Where(field => !field.IsStatic && typeof(IComponent).IsAssignableFrom(field.FieldType))
				.Select(field => new { Field = field, Component = field.GetValue(this) as Component })
				.Where(info => info.Component != null)
				.ToArray();

			_subcomponents = subcomponentMetadata.Select(info => info.Component).ToList();

			for (var i = 0; i < subcomponentMetadata.Length; ++i)
			{
				// Make sure that we won't finalize the same component twice (might happen when components are shared, will be detected later)
				if (!subcomponentMetadata[i].Component.IsMetadataFinalized)
					subcomponentMetadata[i].Component.FinalizeMetadata(this, subcomponentMetadata[i].Field.Name, i, subcomponentMetadata[i].Field);
			}
		}
	}
}