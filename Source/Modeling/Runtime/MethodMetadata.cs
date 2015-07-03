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

	/// <summary>
	///     Represents a base class for the immutable metadata of all S# methods.
	/// </summary>
	public abstract class MethodMetadata
	{
		/// <summary>
		///     The block statement representing the method's body.
		/// </summary>
		private readonly Lazy<MethodBodyMetadata> _methodBody;

		/// <summary>
		///     The S# object the method belongs to.
		/// </summary>
		private readonly IMetadataObject _object;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="obj">The S# object the method belongs to.</param>
		/// <param name="method">The CLR method the metadata should be provided for.</param>
		/// <param name="name">The name of the method; if <c>null</c>, the method's CLR name is used.</param>
		/// <param name="baseMethod">The overridden base method, if any.</param>
		internal MethodMetadata(IMetadataObject obj, MethodInfo method, string name = null, MethodMetadata baseMethod = null)
		{
			Requires.NotNull(obj, () => obj);
			Requires.NotNull(method, () => method);
			Requires.That(name == null || !String.IsNullOrWhiteSpace(name), () => name, "The name must be null or non-whitespace only.");
			Requires.That(baseMethod == null || method != baseMethod.MethodInfo, "A method cannot override itself.");
			Requires.That(baseMethod == null || obj == baseMethod._object, "The base method must belong to the same object.");
			Requires.That(baseMethod == null || baseMethod.OverridingMethod == null, "The base method has already been overridden.");

			_object = obj;

			Name = EscapeName(name ?? method.Name);
			MethodInfo = method;
			BaseMethod = baseMethod;

			if (baseMethod != null)
				baseMethod.OverridingMethod = this;

			var backingFieldAttribute = MethodInfo.GetCustomAttribute<BackingFieldAttribute>();
			if (backingFieldAttribute != null)
				BackingField = backingFieldAttribute.GetFieldInfo(MethodInfo.DeclaringType);

			var behaviorAttribute = MethodInfo.GetCustomAttribute<IntendedBehaviorAttribute>();
			if (behaviorAttribute != null)
				IntendedBehavior = behaviorAttribute.GetMethodInfo(MethodInfo.DeclaringType);

			if (backingFieldAttribute == null && behaviorAttribute == null)
				IntendedBehavior = MethodInfo;

			Behaviors = new MethodBehaviorCollection(obj, this);
			ImplementedMethods = DetermineImplementedInterfaceMethods().ToArray();

			_methodBody = new Lazy<MethodBodyMetadata>(InitializeMethodBody);
		}

		/// <summary>
		///     Gets the behaviors of the method.
		/// </summary>
		public MethodBehaviorCollection Behaviors { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the method is affected by fault effects.
		/// </summary>
		public bool IsAffectedByFaultEffects
		{
			get { return Behaviors != null && Behaviors.IsAffectedByFaultEffects; }
		}

		/// <summary>
		///     Gets the metadata of the fault effects that affect the method.
		/// </summary>
		public IEnumerable<FaultEffectMetadata> FaultEffects
		{
			get
			{
				if (Behaviors == null)
					return Enumerable.Empty<FaultEffectMetadata>();

				return Behaviors.FaultEffects;
			}
		}

		/// <summary>
		///     Gets a value indicating whether the method can be affected by fault effects.
		/// </summary>
		public bool CanBeAffectedByFaultEffects
		{
			get { return BackingField != null; }
		}

		/// <summary>
		///     Gets a value indicating whether the method has an implementation.
		/// </summary>
		internal bool HasImplementation
		{
			get { return IntendedBehavior != null; }
		}

		/// <summary>
		///     Gets the CLR method that represents the method's intended behavior disregarding any active fault effects.
		///     Returns <c>null</c> when <see cref="HasImplementation" /> is <c>false</c>.
		/// </summary>
		internal MethodInfo IntendedBehavior { get; private set; }

		/// <summary>
		///     For methods that can be affected by fault effects, gets the backing field that stores the runtime implementation of the
		///     method. Returns <c>null</c> when <see cref="CanBeAffectedByFaultEffects" /> is <c>false</c>.
		/// </summary>
		internal FieldInfo BackingField { get; private set; }

		/// <summary>
		///     Gets the underlying CLR method.
		/// </summary>
		internal MethodInfo MethodInfo { get; private set; }

		/// <summary>
		///     Gets the metadata of the method's body. Returns <c>null</c> when <see cref="HasImplementation" /> is <c>false</c> or the
		///     method is not analyzable.
		/// </summary>
		public MethodBodyMetadata MethodBody
		{
			get { return _methodBody.Value; }
		}

		/// <summary>
		///     Gets the type of a delegate that can refer to the method. Returns <c>null</c> when
		///     <see cref="CanBeAffectedByFaultEffects" /> is <c>false</c>.
		/// </summary>
		internal Type MethodType
		{
			get
			{
				if (!CanBeAffectedByFaultEffects)
					return null;

				return BackingField.FieldType;
			}
		}

		/// <summary>
		///     Gets the metadata of the overridden base method. Returns <c>null</c> when <see cref="IsOverride" /> is <c>false</c>.
		/// </summary>
		internal MethodMetadata BaseMethod { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the method overrides a method of a base class.
		/// </summary>
		internal bool IsOverride
		{
			get { return BaseMethod != null; }
		}

		/// <summary>
		///     Gets the metadata of the overriding method. Returns <c>null</c> when <see cref="IsOverridden" /> is <c>false</c>.
		/// </summary>
		internal MethodMetadata OverridingMethod { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the method is overridden by another method.
		/// </summary>
		internal bool IsOverridden
		{
			get { return OverridingMethod != null; }
		}

		/// <summary>
		///     Gets the name of the method.
		/// </summary>
		public string Name { get; private set; }

		/// <summary>
		///     Gets the metadata of the declaring object.
		/// </summary>
		public ObjectMetadata DeclaringObject
		{
			get { return _object.Metadata; }
		}

		/// <summary>
		///     Gets the metadata of the method that is invoked by a virtual method invocation.
		/// </summary>
		internal MethodMetadata VirtuallyInvokedMethod
		{
			get
			{
				if (!IsOverridden)
					return this;

				return OverridingMethod.VirtuallyInvokedMethod;
			}
		}

		/// <summary>
		///     Gets the interface methods implemented by the method.
		/// </summary>
		internal IEnumerable<MethodInfo> ImplementedMethods { get; private set; }

		/// <summary>
		///     Initializes the method's <see cref="MethodBodyMetadata" />.
		/// </summary>
		protected virtual MethodBodyMetadata InitializeMethodBody()
		{
			var methodBodyAttribute = MethodInfo.GetCustomAttribute<MethodBodyMetadataAttribute>();
			return methodBodyAttribute == null ? null : methodBodyAttribute.GetMethodBody(_object, MethodInfo);
		}

		/// <summary>
		///     Escapes the <paramref name="methodName" />.
		/// </summary>
		/// <param name="methodName">The method name that should be escaped.</param>
		internal static string EscapeName(string methodName)
		{
			return methodName.Replace(".", "_").Replace("<", "__").Replace(">", "__");
		}

		/// <summary>
		///     Determines the interface methods implemented by the method.
		/// </summary>
		private IEnumerable<MethodInfo> DetermineImplementedInterfaceMethods()
		{
			var type = _object.GetType();
			var interfaceMaps = type.GetInterfaces().Select(implementedInterface => type.GetInterfaceMap(implementedInterface));

			foreach (var interfaceMap in interfaceMaps)
			{
				for (var i = 0; i < interfaceMap.InterfaceMethods.Length; ++i)
				{
					// We can't use == to compare the method infos as their ReflectedType property does not match... how annoying
					var nameMatches = interfaceMap.TargetMethods[i].Name == MethodInfo.Name;
					var returnMatches = interfaceMap.TargetMethods[i].ReturnType == MethodInfo.ReturnType;
					var declaringTypeMatches = interfaceMap.TargetMethods[i].DeclaringType == MethodInfo.DeclaringType;
					var interfaceParameterTypes = interfaceMap.TargetMethods[i].GetParameters().Select(p => p.ParameterType);
					var methodParameterTypes = MethodInfo.GetParameters().Select(p => p.ParameterType);
					var parametersMatch = interfaceParameterTypes.SequenceEqual(methodParameterTypes);

					if (nameMatches && returnMatches && declaringTypeMatches && parametersMatch)
						yield return interfaceMap.InterfaceMethods[i];
				}
			}
		}

		/// <summary>
		///     Gets a delegate to the method that can be used to invoke it on the declaring object.
		/// </summary>
		internal Delegate CreateDelegate(Type delegateType)
		{
			Requires.NotNull(delegateType, () => delegateType);
			return Delegate.CreateDelegate(delegateType, _object, MethodInfo);
		}

		/// <summary>
		///     Returns a string that represents the current object.
		/// </summary>
		public override string ToString()
		{
			return String.Format("{0} declared by {1}", MethodInfo, MethodInfo.DeclaringType);
		}
	}
}