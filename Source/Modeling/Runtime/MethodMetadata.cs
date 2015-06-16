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
	using Utilities;

	/// <summary>
	///     Represents a base class for the immutable metadata of all S# methods.
	/// </summary>
	public abstract class MethodMetadata
	{
		/// <summary>
		///     The S# object the method belongs to.
		/// </summary>
		private readonly object _object;

		/// <summary>
		///     The metadata of the fault effects that affect the method.
		/// </summary>
		private FaultEffectMetadata[] _affectingFaultEffects;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="obj">The S# object the method belongs to.</param>
		/// <param name="method">The CLR method the metadata should be provided for.</param>
		/// <param name="baseMethod">The overridden base method, if any.</param>
		internal MethodMetadata(object obj, MethodInfo method, MethodInfo baseMethod = null)
		{
			Requires.NotNull(obj, () => obj);
			Requires.NotNull(method, () => method);
			Requires.That(method != baseMethod, "A method cannot override itself.");

			_object = obj;
			Method = method;
			BaseMethod = baseMethod;

			var backingFieldAttribute = Method.GetCustomAttribute<BackingFieldAttribute>();
			if (backingFieldAttribute != null)
				BackingField = backingFieldAttribute.GetFieldInfo(Method.DeclaringType);

			var behaviorAttribute = Method.GetCustomAttribute<MethodBehaviorAttribute>();
			if (behaviorAttribute != null)
				Implementation = behaviorAttribute.GetMethodInfo(Method.DeclaringType);

			if (backingFieldAttribute == null && behaviorAttribute == null)
				Implementation = Method;

			if (!HasImplementation || !CanBeAffectedByFaultEffects)
				return;

			var implementationDelegate = Delegate.CreateDelegate(BackingField.FieldType, obj, Implementation);
			BackingField.SetValue(obj, implementationDelegate);
		}

		/// <summary>
		///     Gets a value indicating whether the method is affected by fault effects.
		/// </summary>
		public bool IsAffectedByFaultEffects
		{
			get { return _affectingFaultEffects != null && _affectingFaultEffects.Length > 0; }
		}

		/// <summary>
		///     Gets the metadata of the fault effects that affect the method.
		/// </summary>
		public IEnumerable<FaultEffectMetadata> AffectingFaultEffects
		{
			get
			{
				if (_affectingFaultEffects == null)
				{
					var component = DeclaringObject as ComponentMetadata;
					if (component == null)
						_affectingFaultEffects = new FaultEffectMetadata[0];
					else
					{
						_affectingFaultEffects = component
							.Faults
							.SelectMany(fault => fault.FaultEffects)
							.Where(effect => effect.AffectedMethod.Method == Method)
							.ToArray();
					}
				}

				return _affectingFaultEffects;
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
		public bool HasImplementation
		{
			get { return Implementation != null; }
		}

		/// <summary>
		///     Gets the CLR method that represents the method's implementation disregarding any active fault effects.
		///     Returns <c>null</c> when <see cref="HasImplementation" /> is <c>false</c>.
		/// </summary>
		public MethodInfo Implementation { get; private set; }

		/// <summary>
		///     For methods that can be affected by fault effects, gets the backing field that stores the runtime implementation of the
		///     method. Returns <c>null</c> when <see cref="CanBeAffectedByFaultEffects" /> is <c>false</c>.
		/// </summary>
		public FieldInfo BackingField { get; private set; }

		/// <summary>
		///     Gets the underlying CLR method.
		/// </summary>
		public MethodInfo Method { get; private set; }

		/// <summary>
		///     Gets the overridden base method. Returns <c>null</c> when <see cref="Method" /> does not override any other method.
		/// </summary>
		public MethodInfo BaseMethod { get; private set; }

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
		public string Name
		{
			get { return Method.Name; }
		}

		/// <summary>
		///     Gets the metadata of the declaring object.
		/// </summary>
		public ObjectMetadata DeclaringObject
		{
			get { return _object.GetMetadata(); }
		}

		/// <summary>
		///     Returns a string that represents the current object.
		/// </summary>
		public override string ToString()
		{
			return String.Format("{0} declared by {1}", Method, Method.DeclaringType);
		}
	}
}