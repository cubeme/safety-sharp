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

namespace SafetySharp.Runtime
{
	using System;
	using System.Collections.Generic;
	using System.Collections.Immutable;
	using System.Linq;
	using System.Linq.Expressions;
	using System.Reflection;
	using CompilerServices;
	using Modeling;
	using Utilities;

	partial class ComponentInfo
	{
		/// <summary>
		///     Represents a mutable builder for <see cref="ComponentInfo" /> instances.
		/// </summary>
		public class Builder
		{
			private readonly Component _component;
			private readonly List<FaultInfo> _faults = new List<FaultInfo>();
			private readonly Dictionary<FieldInfo, object[]> _fields = new Dictionary<FieldInfo, object[]>();
			private readonly List<MethodInfo> _requiredPorts = new List<MethodInfo>();
			private readonly List<FieldInfo> _subcomponents = new List<FieldInfo>();
			private string _name;

			/// <summary>
			///     Initializes a new instance.
			/// </summary>
			/// <param name="component">The component instance the metadata should be built for.</param>
			internal Builder(Component component)
			{
				Requires.NotNull(component, () => component);
				_component = component;
			}

			/// <summary>
			///     Adds the <paramref name="field" /> to the component's metadata.
			/// </summary>
			/// <param name="field">The field that should be added to the metadata.</param>
			public void WithField(FieldInfo field)
			{
				Requires.NotNull(field, () => field);
				Requires.That(field.DeclaringType == _component.GetType(), () => field, "The field is not declared by the component.");
				Requires.That(!_fields.ContainsKey(field), () => field, "The field has already been added.");

				_fields.Add(field, null);
			}

			/// <summary>
			///     Sets the initial <paramref name="values" /> of the component's <paramref name="field" />.
			/// </summary>
			/// <param name="field">The field whose initial values should be set.</param>
			/// <param name="values">The initial values of the field.</param>
			public void WithInitialValues(FieldInfo field, params object[] values)
			{
				Requires.NotNull(field, () => field);
				Requires.NotNull(values, () => values);
				Requires.That(values.Length > 0, () => values, "At least one value must be provided.");
				Requires.That(_fields.ContainsKey(field), () => field, "The given field is unknown.");

				var typesMatch = values.All(value => value.GetType() == field.FieldType);
				Requires.That(typesMatch, () => values, "Expected all values to be of type '{0}'.", field.FieldType);

				_fields[field] = values;
			}

			/// <summary>
			///     Adds the subcomponent stored in <see cref="field" /> to the component's metadata.
			/// </summary>
			/// <param name="field">The field holding the subcomponent reference.</param>
			public void WithSubcomponent(FieldInfo field)
			{
				Requires.NotNull(field, () => field);
				Requires.That(field.DeclaringType == _component.GetType(), () => field, "The subcomponent is not declared by the component.");
				Requires.That(!_subcomponents.Contains(field), () => field, "The subcomponent has already been added.");
				Requires.That(typeof(IComponent).IsAssignableFrom(field.FieldType), () => field, "The subcomponent must implement '{0}'.",
					typeof(IComponent).FullName);

				_subcomponents.Add(field);
			}

			/// <summary>
			///     Adds the <paramref name="fault" /> to the component's metadata.
			/// </summary>
			/// <param name="fault">The fault that should be added.</param>
			public void WithFault<T>(T fault)
				where T : Fault
			{
				Requires.NotNull(fault, () => fault);
				Requires.That(!_faults.Any(f => f.Fault is T), () => fault, "The fault has already been added.");

				_faults.Add(MetadataBuilders.GetBuilder(fault).FinalizeMetadata(_component));
			}

			/// <summary>
			///     Adds the <paramref name="providedPort" /> to the component's metadata. If the port overrides a virtual port declared by
			///     a base type, the <paramref name="basePort" /> must not be <c>null</c>. The <paramref name="createBody" /> must not be
			///     <c>null</c> if the component is intended to be used with S# analysis techniques.
			/// </summary>
			/// <param name="providedPort">The provided port that should be added to the component's metadata.</param>
			/// <param name="basePort">The overridden method of the base type, if any.</param>
			/// <param name="createBody">The callback that should be used to retrieve the body of the port.</param>
			public void WithProvidedPort(MethodInfo providedPort, MethodInfo basePort = null, Func<Expression> createBody = null)
			{
				Requires.NotNull(providedPort, () => providedPort);
				Requires.That(providedPort.DeclaringType == _component.GetType(), () => providedPort, "The port is not declared by the component.");
			}

			/// <summary>
			///     Adds the <paramref name="requiredPort" /> to the component's metadata.
			/// </summary>
			public void WithRequiredPort(MethodInfo requiredPort)
			{
				Requires.NotNull(requiredPort, () => requiredPort);
				Requires.That(requiredPort.DeclaringType == _component.GetType(), () => requiredPort, "The port is not declared by the component.");
				Requires.That(!_requiredPorts.Contains(requiredPort), () => requiredPort, "The port has already been added.");

				_requiredPorts.Add(requiredPort);
			}

			/// <summary>
			///     Adds the <paramref name="behavior" /> to the component's metadata. The <paramref name="createBody" /> must not be
			///     <c>null</c> if the component is intended to be used with S# analysis techniques.
			/// </summary>
			/// <param name="behavior">The method representing the component's behavior that should be added to the component's metadata.</param>
			/// <param name="createBody">The callback that should be used to retrieve the body of the method.</param>
			public void WithBehavior(MethodInfo behavior, Func<Expression> createBody = null)
			{
				Requires.NotNull(behavior, () => behavior);
				Requires.That(behavior.DeclaringType == _component.GetType(), () => behavior, "The behavior is not declared by the component.");
			}

			/// <summary>
			///     Adds a binding between <paramref name="targetPort" /> and <paramref name="sourcePort" /> to the component's metadata.
			/// </summary>
			/// <param name="targetPort">The target port of the port binding.</param>
			/// <param name="sourcePort">The source port of the port binding.</param>
			public void WithBinding(Delegate targetPort, Delegate sourcePort)
			{
				Requires.NotNull(targetPort, () => targetPort);
				Requires.NotNull(sourcePort, () => sourcePort);
				Requires.OfType<IComponent>(targetPort.Target, () => targetPort,
					"Expected a port declared by a type implementing '{0}'.", typeof(IComponent).FullName);
				Requires.OfType<IComponent>(targetPort.Target, () => sourcePort,
					"Expected a port declared by a type implementing '{0}'.", typeof(IComponent).FullName);
			}

			/// <summary>
			///     Assigns the <paramref name="name" /> to the component. Within a component hierarchy, all component names must be unique.
			/// </summary>
			/// <param name="name">The name of the component.</param>
			public void WithName(string name)
			{
				Requires.NotNullOrWhitespace(name, () => name);
				_name = name;
			}

			/// <summary>
			///     Creates an immutable <see cref="ComponentInfo" /> instance from the current state of the builder and makes it available
			///     to S#'s <see cref="MetadataProvider" />.
			/// </summary>
			internal ComponentInfo RegisterMetadata()
			{
				var info = new ComponentInfo
				{
					Component = _component,
					Name = _name,
					Faults = _faults.ToImmutableArray()
				};

				MetadataProvider.Components.Add(_component, info);
				MetadataProvider.ComponentBuilders.Remove(_component);

				return info;
			}
		}
	}
}