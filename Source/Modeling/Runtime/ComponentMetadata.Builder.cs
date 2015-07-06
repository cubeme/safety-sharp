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
	using Modeling.Faults;
	using Utilities;

	partial class ComponentMetadata
	{
		/// <summary>
		///   Represents a mutable builder for <see cref="ComponentMetadata" /> instances.
		/// </summary>
		public class Builder
		{
			private readonly Dictionary<MethodInfo, ActionMetadata> _actions = new Dictionary<MethodInfo, ActionMetadata>();
			private readonly List<BindingMetadata> _bindings = new List<BindingMetadata>();
			private readonly Component _component;
			private readonly List<FaultMetadata> _faults = new List<FaultMetadata>();
			private readonly FieldCollectionBuilder _fields;
			private readonly Dictionary<MethodInfo, GuardMetadata> _guards = new Dictionary<MethodInfo, GuardMetadata>();
			private readonly List<StateMetadata> _initialStates = new List<StateMetadata>();
			private readonly NameScope _nameScope = new NameScope();
			private readonly List<ProvidedPortMetadata> _providedPorts = new List<ProvidedPortMetadata>();
			private readonly List<RequiredPortMetadata> _requiredPorts = new List<RequiredPortMetadata>();
			private readonly NameScope _stateNameScope = new NameScope();
			private readonly Dictionary<object, StateMetadata> _states = new Dictionary<object, StateMetadata>();
			private readonly List<StepMethodMetadata> _stepMethods = new List<StepMethodMetadata>();
			private readonly List<FieldInfo> _subcomponentFields = new List<FieldInfo>();
			private readonly List<PropertyInfo> _subcomponentProperties = new List<PropertyInfo>();
			private readonly List<IComponent> _subcomponents = new List<IComponent>();
			private readonly List<TransitionMetadata> _transitions = new List<TransitionMetadata>();
			private string _name;

			/// <summary>
			///   Initializes a new instance.
			/// </summary>
			/// <param name="component">The component instance the metadata should be built for.</param>
			internal Builder(Component component)
			{
				Requires.NotNull(component, () => component);

				_component = component;
				_fields = new FieldCollectionBuilder(component, _nameScope);
			}

			/// <summary>
			///   Adds the <paramref name="field" /> to the component's metadata.
			/// </summary>
			/// <param name="field">The field that should be added to the metadata.</param>
			public void WithField(FieldInfo field)
			{
				_fields.WithField(field);
			}

			/// <summary>
			///   Adds the <paramref name="field" /> of compile-time generic type to the component's metadata. The field
			///   is not added if it is not of a supported field type.
			/// </summary>
			/// <param name="field">The field that should be added to the metadata.</param>
			public void WithGenericField(FieldInfo field)
			{
				_fields.WithGenericField(field);
			}

			/// <summary>
			///   Sets the initial <paramref name="values" /> of the component's <paramref name="field" />.
			/// </summary>
			/// <typeparam name="T">The type of the field.</typeparam>
			/// <param name="field">The field whose initial values should be set.</param>
			/// <param name="values">The initial values of the field.</param>
			public void WithInitialValues<T>(FieldInfo field, params T[] values)
			{
				_fields.WithInitialValues(field, values);
			}

			/// <summary>
			///   Adds the <paramref name="subcomponent" /> to the component's metadata.
			/// </summary>
			/// <param name="subcomponent">The subcomponent that should be added.</param>
			public void WithSubcomponent(IComponent subcomponent)
			{
				Requires.NotNull(subcomponent, () => subcomponent);
				Requires.That(!_subcomponents.Contains(subcomponent), () => subcomponent,
					"The subcomponent has already been added.");
				Requires.OfType<Component>(subcomponent, () => subcomponent);

				_subcomponents.Add(subcomponent);
			}

			/// <summary>
			///   Adds the subcomponent stored in <paramref name="field" /> to the component's metadata.
			/// </summary>
			/// <param name="field">The field holding the subcomponent reference.</param>
			public void WithSubcomponent(FieldInfo field)
			{
				Requires.NotNull(field, () => field);
				Requires.That(!_subcomponentFields.Contains(field), () => field, "The subcomponent has already been added.");
				Requires.That(typeof(IComponent).IsAssignableFrom(field.FieldType), () => field, "The subcomponent must implement '{0}'.",
					typeof(IComponent).FullName);

				_subcomponentFields.Add(field);
			}

			/// <summary>
			///   Adds the subcomponent of compile-time generic type stored in <paramref name="field" /> to the component's metadata. The
			///   subcomponent is not added if it actually wasn't an <see cref="IComponent" />-derived type.
			/// </summary>
			/// <param name="field">The field holding the subcomponent reference.</param>
			public void WithGenericSubcomponent(FieldInfo field)
			{
				Requires.NotNull(field, () => field);

				if (typeof(IComponent).IsAssignableFrom(field.FieldType))
					WithSubcomponent(field);
			}

			/// <summary>
			///   Adds the subcomponent stored in <paramref name="property" /> to the component's metadata.
			/// </summary>
			/// <param name="property">The property holding the subcomponent reference.</param>
			public void WithSubcomponent(PropertyInfo property)
			{
				Requires.NotNull(property, () => property);
				Requires.That(!_subcomponentProperties.Contains(property), () => property, "The subcomponent has already been added.");
				Requires.That(property.CanRead, () => property, "The property must be readable.");
				Requires.That(typeof(IComponent).IsAssignableFrom(property.PropertyType), () => property, "The subcomponent must implement '{0}'.",
					typeof(IComponent).FullName);

				_subcomponentProperties.Add(property);
			}

			/// <summary>
			///   Adds the subcomponent of compile-time generic type stored in <paramref name="property" /> to the component's metadata.
			///   The subcomponent is not added if it actually wasn't an <see cref="IComponent" />-derived type.
			/// </summary>
			/// <param name="property">The property holding the subcomponent reference.</param>
			public void WithGenericSubcomponent(PropertyInfo property)
			{
				Requires.NotNull(property, () => property);

				if (typeof(IComponent).IsAssignableFrom(property.PropertyType))
					WithSubcomponent(property);
			}

			/// <summary>
			///   Adds the <paramref name="fault" /> to the component's metadata.
			/// </summary>
			/// <typeparam name="TFault">The type of the fault that should be added to the component's metadata.</typeparam>
			/// <param name="fault">The fault that should be added.</param>
			public void WithFault<TFault>(TFault fault)
				where TFault : Fault
			{
				Requires.NotNull(fault, () => fault);
				Requires.That(!_faults.Any(f => f.Fault is TFault), () => fault, "The fault has already been added.");

				fault.Component = _component;
				fault.MetadataBuilder.FinalizeMetadata(_component);

				_faults.Add(fault.Metadata);
			}

			/// <summary>
			///   Adds the <paramref name="providedPort" /> to the component's metadata. If the port overrides a virtual port declared by
			///   a base type, the <paramref name="basePort" /> must not be <c>null</c>.
			/// </summary>
			/// <param name="providedPort">The provided port that should be added to the component's metadata.</param>
			/// <param name="basePort">The overridden method of the base type, if any.</param>
			public void WithProvidedPort(MethodInfo providedPort, MethodInfo basePort = null)
			{
				Requires.NotNull(providedPort, () => providedPort);
				Requires.That(_providedPorts.All(port => port.MethodInfo != providedPort), () => providedPort,
					"The port has already been added.");
				Requires.That(providedPort.HasAttribute<ProvidedAttribute>(), () => providedPort,
					"The method must be marked with'{0}'.", typeof(ProvidedAttribute).FullName);

				ProvidedPortMetadata baseMetadata = null;
				if (basePort != null)
				{
					baseMetadata = _providedPorts.SingleOrDefault(port => port.MethodInfo == basePort);
					Requires.That(baseMetadata != null, () => basePort, "The base port is unknown.");
				}

				var name = _nameScope.MakeUnique(MethodMetadata.EscapeName(providedPort.Name));
				_providedPorts.Add(new ProvidedPortMetadata(_component, providedPort, name, baseMetadata));
			}

			/// <summary>
			///   Adds the <paramref name="requiredPort" /> to the component's metadata.
			/// </summary>
			public void WithRequiredPort(MethodInfo requiredPort)
			{
				Requires.NotNull(requiredPort, () => requiredPort);
				Requires.That(_requiredPorts.All(port => port.MethodInfo != requiredPort), () => requiredPort,
					"The port has already been added.");
				Requires.That(requiredPort.HasAttribute<RequiredAttribute>(), () => requiredPort,
					"The method must be marked with'{0}'.", typeof(RequiredAttribute).FullName);

				var name = _nameScope.MakeUnique(MethodMetadata.EscapeName(requiredPort.Name));
				_requiredPorts.Add(new RequiredPortMetadata(_component, requiredPort, name));
			}

			/// <summary>
			///   Adds the <paramref name="stepMethod" /> to the component's metadata. If <paramref name="stepMethod" /> overrides a step
			///   method declared by a base type, the <paramref name="baseStepMethod" /> must not be <c>null</c>.
			/// </summary>
			/// <param name="stepMethod">
			///   The method representing the component's step method that should be added to the component's metadata.
			/// </param>
			/// <param name="baseStepMethod">The overridden step method of the base type, if any.</param>
			public void WithStepMethod(MethodInfo stepMethod, MethodInfo baseStepMethod = null)
			{
				Requires.NotNull(stepMethod, () => stepMethod);
				Requires.That(baseStepMethod == null || _stepMethods.Any(method => method.MethodInfo == baseStepMethod),
					() => baseStepMethod, "The base step method is unknown.");

				var baseMetadata = baseStepMethod != null ? _stepMethods.Single(method => method.MethodInfo == baseStepMethod) : null;
				var metadata = new StepMethodMetadata(_component, stepMethod, baseMetadata);

				Requires.That(metadata.CanBeAffectedByFaultEffects, () => stepMethod, "Component step methods must be sensitive to fault effects.");
				_stepMethods.Add(metadata);
			}

			/// <summary>
			///   Adds a binding between <paramref name="requiredPort" /> and <paramref name="providedPort" /> to the component's
			///   metadata.
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

				_bindings.Add(new BindingMetadata(_component, requiredPort, providedPort));
			}

			/// <summary>
			///   Assigns the <paramref name="name" /> to the component. Within a component hierarchy, all component names must be unique.
			/// </summary>
			/// <param name="name">The name of the component.</param>
			/// <param name="compilerGenerated">
			///   Indicates whether the name was generated by the S# compiler. If <c>true</c>,
			///   <paramref name="name" /> is ignored if another name has already been set.
			/// </param>
			public void WithName(string name, bool compilerGenerated = false)
			{
				Requires.NotNullOrWhitespace(name, () => name);

				if (!compilerGenerated || String.IsNullOrWhiteSpace(_name))
					_name = name;
			}

			/// <summary>
			///   Indicates that the component's state machine can initially be in the <paramref name="initialStates" />.
			/// </summary>
			/// <param name="initialStates">Some of the initial states of the state machine.</param>
			public void WithInitialStates(params object[] initialStates)
			{
				Requires.NotNull(initialStates, () => initialStates);

				foreach (var initialState in initialStates)
				{
					Requires.That(initialState.GetType().IsEnum, () => initialStates, "Expected enum values.");
					_initialStates.Add(GetOrAddState(initialState));
				}
			}

			/// <summary>
			///   Adds a transition to the component's finite state machine.
			/// </summary>
			/// <param name="sourceState">The source state that should be left by the transition.</param>
			/// <param name="targetState">The target state that should be entered by the transition.</param>
			/// <param name="guard">The guard that determines whether the transition can be taken.</param>
			/// <param name="action">The action that should be executed when the transition is taken.</param>
			public void WithTransition(object sourceState, object targetState, MethodInfo guard, MethodInfo action)
			{
				Requires.NotNull(sourceState, () => sourceState);
				Requires.NotNull(targetState, () => targetState);
				Requires.That(sourceState.GetType().IsEnum, () => sourceState, "Expected an enum value.");
				Requires.That(targetState.GetType().IsEnum, () => targetState, "Expected an enum value.");

				var source = GetOrAddState(sourceState);
				var target = GetOrAddState(targetState);
				GuardMetadata guardMetadata = null;
				ActionMetadata actionMetadata = null;

				if (guard != null && !_guards.TryGetValue(guard, out guardMetadata))
					_guards.Add(guard, guardMetadata = new GuardMetadata(_component, guard, _nameScope.MakeUnique(guard.Name)));

				if (action != null && !_actions.TryGetValue(action, out actionMetadata))
					_actions.Add(action, actionMetadata = new ActionMetadata(_component, action, _nameScope.MakeUnique(action.Name)));

				_transitions.Add(new TransitionMetadata(_component, source, target, guardMetadata, actionMetadata));
			}

			/// <summary>
			///   Gets the <see cref="StateMetadata" /> instance corresponding targetState the <paramref name="state" /> if
			///   <paramref name="state" /> is already known; creates a new instance otherwise.
			/// </summary>
			private StateMetadata GetOrAddState(object state)
			{
				StateMetadata metadata;
				if (!_states.TryGetValue(state, out metadata))
				{
					metadata = new StateMetadata(_component, _states.Count, _stateNameScope.MakeUnique(state.ToString()), state);
					_states.Add(state, metadata);
				}

				return metadata;
			}

			/// <summary>
			///   Creates an immutable <see cref="ComponentMetadata" /> instance from the current state of the builder.
			/// </summary>
			/// <param name="name">The automatically generated name of the component.</param>
			/// <param name="parent">The metadata of the parent component. Can be <c>null</c> for the root of the component hierarchy.</param>
			internal void FinalizeMetadata(string name = null, ComponentMetadata parent = null)
			{
				// We have to register the metadata now, even though we'll still have to change it later on; this way,
				// we prevent stack overflows when the component hierarchy is cyclic
				_component.Metadata = new ComponentMetadata
				{
					Component = _component,
					Name = String.IsNullOrWhiteSpace(_name) ? name : _name,
					ParentComponent = parent,
					Fields = _fields.ToImmutableCollection(),
					Faults = new MemberCollection<FaultMetadata>(_component, _faults),
					UpdateMethods = new MemberCollection<StepMethodMetadata>(_component, _stepMethods),
					StepMethod = (StepMethodMetadata)_stepMethods[0].VirtuallyInvokedMethod,
					RequiredPorts = new MemberCollection<RequiredPortMetadata>(_component, _requiredPorts),
					ProvidedPorts = new MemberCollection<ProvidedPortMetadata>(_component, _providedPorts),
					Bindings = new MemberCollection<BindingMetadata>(_component, _bindings),
				};

				if (_transitions.Count > 0)
				{
					var fieldInfo = ReflectionHelpers.GetField(typeof(Component), typeof(int), "_state");
					var initialValues = _initialStates.Select(state => state.Identifier).Cast<object>().Distinct().ToArray();
					var stateField = new FieldMetadata(_component, fieldInfo, initialValues, _nameScope.MakeUnique(fieldInfo.Name));

					_component.Metadata.StateMachine = new StateMachineMetadata(_component, stateField, _states.Values, _initialStates, _transitions);
				}

				InitializeFaults();
				InitializeSubcomponents();
			}

			/// <summary>
			///   Initializes the component's fault injections.
			/// </summary>
			private void InitializeFaults()
			{
				_component.Metadata.UpdateMethods.ForEach(stepMethod => stepMethod.Behaviors.InjectFaults());
				_component.Metadata.RequiredPorts.ForEach(port => port.Behaviors.InjectFaults());
				_component.Metadata.ProvidedPorts.ForEach(port => port.Behaviors.InjectFaults());
			}

			/// <summary>
			///   Initializes the component's subcomponents.
			/// </summary>
			private void InitializeSubcomponents()
			{
				var nameScope = new NameScope();

				// Get all subcomponent instances
				var fromFields = _subcomponentFields
					.Select(field =>
					{
						var component = field.GetValue(_component) as Component;
						Requires.That(component != null, "Subcomponent field '{0}.{1}' does not contain a valid component instance.",
							field.DeclaringType.FullName, field.Name);

						return new { Component = component, Name = nameScope.MakeUnique(field.Name) };
					});

				var fromProperties = _subcomponentProperties.Select(property =>
				{
					var component = property.GetValue(_component) as Component;
					Requires.That(component != null, "Subcomponent property '{0}.{1}' does not contain a valid component instance.",
						property.DeclaringType.FullName, property.Name);

					return new { Component = component, Name = nameScope.MakeUnique(property.Name) };
				});

				var fromInstance = _subcomponents.Select(subcomponent =>
					new { Component = (Component)subcomponent, Name = nameScope.MakeUnique(subcomponent.GetType().Name) });

				var subcomponents = fromFields.Concat(fromProperties).Concat(fromInstance);

				// Initialize their metadata, if that hasn't happened already (i.e., when the component graph is cyclic)
				foreach (var subcomponent in subcomponents.Where(subcomponent => !subcomponent.Component.IsMetadataFinalized))
					subcomponent.Component.MetadataBuilder.FinalizeMetadata(subcomponent.Name, _component.Metadata);

				// Add the subcomponents to the metadata
				var subcomponentMetadata = subcomponents.Select(subcomponent => subcomponent.Component.Metadata);
				_component.Metadata.Subcomponents = new MemberCollection<ComponentMetadata>(_component, subcomponentMetadata);
			}
		}
	}
}