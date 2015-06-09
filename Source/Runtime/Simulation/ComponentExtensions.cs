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

namespace SafetySharp.Runtime.Simulation
{
	using System;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Provides extension methods for analyzing <see cref="Component" /> instances.
	/// </summary>
	public static class ComponentExtensions
	{
		/// <summary>
		///     Resets the state of the <paramref name="component" />, i.e., resets all fields and faults to their initial values.
		/// </summary>
		/// <param name="component">The component whose state should be reset.</param>
		internal static void Reset(this Component component)
		{
			Requires.NotNull(component, () => component);
			component.RequiresIsSealed();

			// TODO: What about fields with nondeterministic initial values
			// TODO: Requires tests
			foreach (var field in component.Fields)
				field.Key.SetValue(component, field.Value[0]);

			// TODO: Respect other initial states
			foreach (var fault in component.Faults)
				fault.Occurring = false;
		}

		/// <summary>
		///     Updates the occurrence patterns and internal state of all faults of the <paramref name="component" />.
		/// </summary>
		/// <param name="component">The component whose faults should be updated.</param>
		internal static void UpdateFaults(this Component component)
		{
			Requires.NotNull(component, () => component);
			component.RequiresIsSealed();

			foreach (var fault in component.Faults)
				fault.Update();
		}

		/// <summary>
		///     Gets a value indicating whether the fault of type <typeparamref name="T" /> is currently occurring for the
		///     <paramref name="component" /> instance.
		/// </summary>
		/// <typeparam name="T">The type of the fault that should be checked.</typeparam>
		/// <param name="component">The component instance that should be checked.</param>
		public static bool IsFaultEnabled<T>(this Component component)
			where T : Fault
		{
			Requires.NotNull(component, () => component);
			return component.GetFault<T>().Occurring;
		}

		/// <summary>
		///     Enables or disables the fault of type <typeparamref name="T" /> for the <paramref name="component" /> instance.
		/// </summary>
		/// <typeparam name="T">The type of the fault that should be enabled or disabled.</typeparam>
		/// <param name="component">The component instance the fault should be enabled or disabled for.</param>
		/// <param name="enabled">Indicates whether the fault is enabled.</param>
		public static void SetFaultEnabled<T>(this Component component, bool enabled)
			where T : Fault
		{
			Requires.NotNull(component, () => component);
			component.GetFault<T>().Occurring = enabled;
		}

		/// <summary>
		///     Enables the fault of type <typeparamref name="T" /> for the <paramref name="component" /> instance.
		/// </summary>
		/// <typeparam name="T">The type of the fault that should be enabled.</typeparam>
		/// <param name="component">The component instance the fault should be enabled for.</param>
		public static void EnableFault<T>(this Component component)
			where T : Fault
		{
			Requires.NotNull(component, () => component);
			component.GetFault<T>().Occurring = true;
		}

		/// <summary>
		///     Disables the fault of type <typeparamref name="T" /> for the <paramref name="component" /> instance.
		/// </summary>
		/// <typeparam name="T">The type of the fault that should be disabled.</typeparam>
		/// <param name="component">The component instance the fault should be disabled for.</param>
		public static void DisableFault<T>(this Component component)
			where T : Fault
		{
			Requires.NotNull(component, () => component);
			component.GetFault<T>().Occurring = false;
		}
	}
}