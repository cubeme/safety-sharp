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
	using Modeling;
	using Modeling.Faults;

	/// <summary>
	///     Represents the immutable metadata of a S# <see cref="Fault" /> instance.
	/// </summary>
	public sealed partial class FaultMetadata : ObjectMetadata
	{
		/// <summary>
		///     The component affected by the fault.
		/// </summary>
		private Component _component;

		/// <summary>
		///     Gets the metadata of the declaring component.
		/// </summary>
		public ComponentMetadata DeclaringComponent
		{
			get { return _component.GetMetadata(); }
		}

		/// <summary>
		///     Gets the fault the metadata is provided for.
		/// </summary>
		public Fault Fault { get; private set; }

		/// <summary>
		///     Gets the fault effects declared by the fault.
		/// </summary>
		public MemberCollection<FaultEffectMetadata> FaultEffects { get; private set; }

		/// <summary>
		///     Gets the step methods declared by the fault.
		/// </summary>
		public MemberCollection<StepMethodMetadata> StepMethods { get; private set; }

		/// <summary>
		///     Gets the fields declared by the fault.
		/// </summary>
		public MemberCollection<FieldMetadata> Fields { get; private set; }

		/// <summary>
		///     Gets the metadata of the occurrence pattern determining the fault's occurrence.
		/// </summary>
		public OccurrencePatternMetadata OccurrencePattern { get; private set; }

		/// <summary>
		///     Gets the name of the fault.
		/// </summary>
		public string Name
		{
			get { return Fault.GetType().Name; }
		}
	}
}