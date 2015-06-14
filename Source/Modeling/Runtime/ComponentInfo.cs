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

	/// <summary>
	///     Represents the immutable metadata of a S# <see cref="Component" /> instance.
	/// </summary>
	public sealed partial class ComponentInfo
	{
		/// <summary>
		///     Gets the faults affecting the component.
		/// </summary>
		public ComponentMemberCollection<FaultInfo> Faults { get; private set; }

		/// <summary>
		///     Gets the fields declared by the component.
		/// </summary>
		public ComponentMemberCollection<ComponentFieldInfo> Fields { get; private set; }

		/// <summary>
		///     Gets the port bindings declared by the component.
		/// </summary>
		public ComponentMemberCollection<BindingInfo> Bindings { get; private set; }

		/// <summary>
		///     Gets the subcomponents contained within the component.
		/// </summary>
		public ComponentMemberCollection<ComponentInfo> Subcomponents { get; private set; }

		/// <summary>
		///     Gets the <see cref="Component" /> instance the metadata is provided for.
		/// </summary>
		public Component Component { get; private set; }

		/// <summary>
		///     Gets the parent <see cref="Component" /> instance within the component hierarchy. Returns <c>null</c> for the
		///     root component.
		/// </summary>
		public ComponentInfo ParentComponent { get; private set; }

		/// <summary>
		///     Gets the behaviors declared by the component.
		/// </summary>
		public ComponentMethodCollection<BehaviorInfo> Behaviors { get; private set; }

		/// <summary>
		///     Gets the required ports declared by the component.
		/// </summary>
		public ComponentMethodCollection<RequiredPortInfo> RequiredPorts { get; private set; }

		/// <summary>
		///     Gets the provided ports declared by the component.
		/// </summary>
		public ComponentMethodCollection<ProvidedPortInfo> ProvidedPorts { get; private set; }

		/// <summary>
		///     Gets the user-friendly name of the component.
		/// </summary>
		public string Name { get; private set; }
	}
}