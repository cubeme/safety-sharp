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

			_object = obj;

			Name = name ?? method.Name;
			MethodInfo = method;
			BaseMethod = baseMethod;

			var backingFieldAttribute = MethodInfo.GetCustomAttribute<BackingFieldAttribute>();
			if (backingFieldAttribute != null)
				BackingField = backingFieldAttribute.GetFieldInfo(MethodInfo.DeclaringType);

			var behaviorAttribute = MethodInfo.GetCustomAttribute<IntendedBehaviorAttribute>();
			if (behaviorAttribute != null)
				IntendedBehavior = behaviorAttribute.GetMethodInfo(MethodInfo.DeclaringType);

			if (backingFieldAttribute == null && behaviorAttribute == null)
				IntendedBehavior = MethodInfo;

			if (BackingField != null)
				FaultInjector = new FaultInjector(obj, this);
		}

		/// <summary>
		///     Gets the fault injector that injects fault effects into the undependable method. Returns <c>null</c> if
		///     <see cref="CanBeAffectedByFaultEffects" /> is <c>false</c>.
		/// </summary>
		public FaultInjector FaultInjector { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the method is affected by fault effects.
		/// </summary>
		public bool IsAffectedByFaultEffects
		{
			get { return FaultInjector != null && FaultInjector.IsAffectedByFaultEffects; }
		}

		/// <summary>
		///     Gets the metadata of the fault effects that affect the method.
		/// </summary>
		public IEnumerable<FaultEffectMetadata> AffectingFaultEffects
		{
			get
			{
				if (FaultInjector == null)
					return Enumerable.Empty<FaultEffectMetadata>();

				return FaultInjector.AffectingFaultEffects;
			}
		}

		/// <summary>
		///     Gets a value indicating whether the method can be affected by fault effects.
		/// </summary>
		public bool CanBeAffectedByFaultEffects
		{
			get { return FaultInjector != null; }
		}

		/// <summary>
		///     Gets a value indicating whether the method has an implementation.
		/// </summary>
		public bool HasImplementation
		{
			get { return IntendedBehavior != null; }
		}

		/// <summary>
		///     Gets the CLR method that represents the method's intended behavior disregarding any active fault effects.
		///     Returns <c>null</c> when <see cref="HasImplementation" /> is <c>false</c>.
		/// </summary>
		public MethodInfo IntendedBehavior { get; private set; }

		/// <summary>
		///     For methods that can be affected by fault effects, gets the backing field that stores the runtime implementation of the
		///     method. Returns <c>null</c> when <see cref="CanBeAffectedByFaultEffects" /> is <c>false</c>.
		/// </summary>
		public FieldInfo BackingField { get; private set; }

		/// <summary>
		///     Gets the underlying CLR method.
		/// </summary>
		public MethodInfo MethodInfo { get; private set; }

		/// <summary>
		///     Gets the type of a delegate that can refer to the method. Returns <c>null</c> when
		///     <see cref="CanBeAffectedByFaultEffects" /> is <c>false</c>.
		/// </summary>
		public Type MethodType
		{
			get
			{
				if (!CanBeAffectedByFaultEffects)
					return null;

				return BackingField.FieldType;
			}
		}

		/// <summary>
		///     Gets the overridden base method. Returns <c>null</c> when <see cref="MethodInfo" /> does not override any other method.
		/// </summary>
		public MethodMetadata BaseMethod { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the method overrides a method of a base class.
		/// </summary>
		public bool IsOverride
		{
			get { return BaseMethod != null; }
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
		///     Gets a delegate to the method that can be used to invoke it on the declaring object.
		/// </summary>
		public Delegate CreateDelegate(Type delegateType)
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