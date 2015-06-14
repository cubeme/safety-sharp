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
	using System.Linq;
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
			private readonly List<BindingInfo> _bindings = new List<BindingInfo>();
			private readonly Component _component;
			private readonly List<FaultInfo> _faults = new List<FaultInfo>();
			private readonly Dictionary<FieldInfo, object[]> _fields = new Dictionary<FieldInfo, object[]>();
			private readonly List<ProvidedPortInfo> _providedPorts = new List<ProvidedPortInfo>();
			private readonly List<RequiredPortInfo> _requiredPorts = new List<RequiredPortInfo>();
			private readonly List<StepMethodInfo> _stepMethods = new List<StepMethodInfo>();
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
				Requires.That(!_fields.ContainsKey(field), () => field, "The field has already been added.");
				Requires.That(field.FieldType == typeof(int) || field.FieldType == typeof(bool) ||
							  field.FieldType == typeof(double) || field.FieldType.IsEnum, () => field,
					"Invalid field type: Only 'bool', 'int', 'double', and enumeration types are supported.");

				_fields.Add(field, null);
			}

			/// <summary>
			///     Adds the <paramref name="field" /> of compile-time generic type to the component's metadata. The field
			///     is not added if it is not of a supported field type.
			/// </summary>
			/// <param name="field">The field that should be added to the metadata.</param>
			public void WithGenericField(FieldInfo field)
			{
				Requires.NotNull(field, () => field);
				Requires.That(!_fields.ContainsKey(field), () => field, "The field has already been added.");

				if (field.FieldType == typeof(int) || field.FieldType == typeof(bool) || field.FieldType == typeof(double) || field.FieldType.IsEnum)
					WithField(field);
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
				Requires.That(!_subcomponents.Contains(field), () => field, "The subcomponent has already been added.");
				Requires.That(typeof(IComponent).IsAssignableFrom(field.FieldType), () => field, "The subcomponent must implement '{0}'.",
					typeof(IComponent).FullName);

				_subcomponents.Add(field);
			}

			/// <summary>
			///     Adds the subcomponent of compile-time generic type stored in <see cref="field" /> to the component's metadata. The
			///     subcomponent is not added if it actually wasn't a subcomponent.
			/// </summary>
			/// <param name="field">The field holding the subcomponent reference.</param>
			public void WithGenericSubcomponent(FieldInfo field)
			{
				Requires.NotNull(field, () => field);
				Requires.That(!_subcomponents.Contains(field), () => field, "The subcomponent has already been added.");

				if (typeof(IComponent).IsAssignableFrom(field.FieldType))
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

				_faults.Add(MetadataBuilders.GetBuilder(fault).RegisterMetadata(_component));
			}

			/// <summary>
			///     Adds the <paramref name="providedPort" /> to the component's metadata. If the port overrides a virtual port declared by
			///     a base type, the <paramref name="basePort" /> must not be <c>null</c>.
			/// </summary>
			/// <param name="providedPort">The provided port that should be added to the component's metadata.</param>
			/// <param name="basePort">The overridden method of the base type, if any.</param>
			public void WithProvidedPort(MethodInfo providedPort, MethodInfo basePort = null)
			{
				Requires.NotNull(providedPort, () => providedPort);
				Requires.That(_providedPorts.All(p => p.Method != providedPort), () => providedPort, "The port has already been added.");
				Requires.That(providedPort.HasAttribute<ProvidedAttribute>(), () => providedPort,
					"The method must be marked with'{0}'.", typeof(ProvidedAttribute).FullName);
				Requires.That(basePort == null || _providedPorts.Any(p => p.Method == basePort), () => _providedPorts,
					"The base port is unknown.");

				_providedPorts.Add(new ProvidedPortInfo(_component, providedPort, basePort));
			}

			/// <summary>
			///     Adds the <paramref name="requiredPort" /> to the component's metadata.
			/// </summary>
			public void WithRequiredPort(MethodInfo requiredPort)
			{
				Requires.NotNull(requiredPort, () => requiredPort);
				Requires.That(_requiredPorts.All(p => p.Method != requiredPort), () => requiredPort, "The port has already been added.");
				Requires.That(requiredPort.HasAttribute<RequiredAttribute>(), () => requiredPort,
					"The method must be marked with'{0}'.", typeof(RequiredAttribute).FullName);

				_requiredPorts.Add(new RequiredPortInfo(_component, requiredPort));
			}

			/// <summary>
			///     Adds the <paramref name="stepMethod" /> to the component's metadata. If <paramref name="stepMethod" /> overrides a step
			///     method declared by a base type, the <paramref name="baseStepMethod" /> must not be <c>null</c>.
			/// </summary>
			/// <param name="stepMethod">The method representing the component's behavior that should be added to the component's metadata.</param>
			/// <param name="baseStepMethod">The overridden behavior of the base type, if any.</param>
			public void WithStepMethod(MethodInfo stepMethod, MethodInfo baseStepMethod = null)
			{
				Requires.NotNull(stepMethod, () => stepMethod);
				Requires.That(baseStepMethod == null || _stepMethods.Any(b => b.Method == baseStepMethod), () => baseStepMethod,
					"The base behavior is unknown.");

				_stepMethods.Add(new StepMethodInfo(_component, stepMethod, baseStepMethod));
			}

			/// <summary>
			///     Adds a binding between <paramref name="requiredPort" /> and <paramref name="providedPort" /> to the component's
			///     metadata.
			/// </summary>
			/// <param name="requiredPort">The required port of the port binding.</param>
			/// <param name="providedPort">The provided port of the port binding.</param>
			public void WithBinding(Delegate requiredPort, Delegate providedPort)
			{
				Requires.NotNull(requiredPort, () => requiredPort);
				Requires.NotNull(providedPort, () => providedPort);
				Requires.OfType<IComponent>(requiredPort.Target, () => requiredPort,
					"Expected a port declared by a type implementing '{0}'.", typeof(IComponent).FullName);
				Requires.OfType<IComponent>(requiredPort.Target, () => providedPort,
					"Expected a port declared by a type implementing '{0}'.", typeof(IComponent).FullName);
				Requires.That(requiredPort.Method.HasAttribute<RequiredAttribute>(), () => requiredPort,
					"Expected a required port declared by a type implementing '{0}'.", typeof(IComponent).FullName);
				Requires.That(providedPort.Method.HasAttribute<ProvidedAttribute>(), () => providedPort,
					"Expected a provided port declared by a type implementing '{0}'.", typeof(IComponent).FullName);

				_bindings.Add(new BindingInfo(_component, requiredPort, providedPort));
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
			/// <param name="parent">The metadata of the parent component. Can be <c>null</c> for the root of the component hierarchy.</param>
			internal ComponentInfo RegisterMetadata(ComponentInfo parent = null)
			{
				var fields = _fields.Select(field => new ComponentFieldInfo(_component, field.Key, field.Value));
				var info = new ComponentInfo
				{
					Component = _component,
					Name = _name,
					ParentComponent = parent,
					Fields = new ComponentMemberCollection<ComponentFieldInfo>(_component, fields),
					Faults = new ComponentMemberCollection<FaultInfo>(_component, _faults),
					Behaviors = new ComponentMethodCollection<BehaviorInfo>(_component, _stepMethods),
					RequiredPorts = new ComponentMethodCollection<RequiredPortInfo>(_component, _requiredPorts),
					ProvidedPorts = new ComponentMethodCollection<ProvidedPortInfo>(_component, _providedPorts),
					Bindings = new ComponentMemberCollection<BindingInfo>(_component, _bindings)
				};

				// Get all subcomponent instances
				var subcomponents = _subcomponents.Select(field =>
				{
					var component = field.GetValue(_component) as Component;
					Requires.That(component != null, "Subcomponent field '{0}.{1}' does not contain a valid component instance.",
						field.DeclaringType.FullName, field.Name);

					return component;
				});

				// Initialize their metadata, if that hasn't happened already (i.e., when the component graph is cyclic)
				foreach (var subcomponent in subcomponents)
				{
					object builder;
					if (MetadataProvider.TryGetBuilder(subcomponent, out builder))
						((Builder)builder).RegisterMetadata(info);
				}

				// Add the subcomponents to the metadata
				var subcomponentMetadata = subcomponents.Select(subcomponent => subcomponent.GetComponentInfo());
				info.Subcomponents = new ComponentMemberCollection<ComponentInfo>(_component, subcomponentMetadata);

				MetadataProvider.FinalizeMetadata(_component, info);
				return info;
			}
		}
	}
}