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

namespace SafetySharp.Runtime.Modeling
{
	using System;
	using System.Collections.Immutable;
	using System.Diagnostics;
	using System.Linq;
	using System.Reflection;
	using Utilities;

	partial class Component
	{
		/// <summary>
		///     The list of faults that affect the component.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private ImmutableArray<Fault> _faults;

		/// <summary>
		///     Gets the faults of the component.
		/// </summary>
		internal ImmutableArray<Fault> Faults
		{
			get
			{
				RequiresIsSealed();
				return _faults;
			}
		}

		/// Gets the fault of the given type.
		internal Fault GetFault<T>()
			where T : Fault
		{
			var fault = _faults.OfType<T>().FirstOrDefault();
			Requires.That(fault != null, "The component does not declare a fault of type '%s'.", typeof(T).FullName);

			return fault;
		}

		/// <summary>
		///     Initializes the faults that affect the component.
		/// </summary>
		private void InitializeFaults()
		{
			_faults = GetType()
				.GetNestedTypes(BindingFlags.FlattenHierarchy | BindingFlags.Public | BindingFlags.NonPublic)
				.Where(t => t.IsClass && typeof(Fault).IsAssignableFrom(t))
				.Select(t => Activator.CreateInstance(t) as Fault)
				.ToImmutableArray();

			foreach (var fault in _faults)
				fault.Initialize(this);
		}
	}
}