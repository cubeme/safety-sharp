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
	using System.Linq;
	using System.Reflection;
	using Modeling;
	using Modeling.Faults;
	using Utilities;

	/// <summary>
	///     Represents the immutable metadata of a S# fault effect.
	/// </summary>
	public sealed class FaultEffectMetadata : MethodMetadata
	{
		/// <summary>
		///     The CLR method representing the affected method.
		/// </summary>
		private readonly MethodInfo _affectedMethod;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="fault">The fault the fault effect belongs to.</param>
		/// <param name="faultEffect">The CLR method the metadata is provided for.</param>
		/// <param name="affectedMethod">The CLR method representing the method affected by the fault effect.</param>
		internal FaultEffectMetadata(Fault fault, MethodInfo faultEffect, MethodInfo affectedMethod)
			: base(fault, faultEffect)
		{
			Requires.NotNull(fault, () => fault);
			Requires.NotNull(faultEffect, () => faultEffect);
			Requires.NotNull(affectedMethod, () => affectedMethod);

			_affectedMethod = affectedMethod;

			var priorityAttribute = faultEffect.GetCustomAttribute<PriorityAttribute>();
			if (priorityAttribute != null)
				Priority = priorityAttribute.Priority;
		}

		/// <summary>
		///     Gets the metadata of the declaring fault.
		/// </summary>
		public FaultMetadata DeclaringFault
		{
			get { return (FaultMetadata)DeclaringObject; }
		}

		/// <summary>
		///     Gets the priority of the fault effect. Fault effect with higher priority values
		///     take precedence over fault effects with lower values when both fault effects affect
		///     the same method at the same time.
		/// </summary>
		public int Priority { get; private set; }

		/// <summary>
		///     Gets the metadata of the affected method.
		/// </summary>
		public MethodMetadata AffectedMethod
		{
			get
			{
				var component = DeclaringFault.DeclaringComponent;

				MethodMetadata metadata = component.ProvidedPorts.SingleOrDefault(port => port.MethodInfo == _affectedMethod);
				if (metadata != null)
					return metadata;

				metadata = component.RequiredPorts.SingleOrDefault(port => port.MethodInfo == _affectedMethod);
				if (metadata != null)
					return metadata;

				metadata = component.StepMethods.SingleOrDefault(step => step.MethodInfo == _affectedMethod);
				if (metadata != null)
					return metadata;

				Assert.NotReached("Failed to find the method affected by the fault effect.");
				return null;
			}
		}
	}
}