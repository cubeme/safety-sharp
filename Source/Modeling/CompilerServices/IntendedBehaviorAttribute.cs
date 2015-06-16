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

namespace SafetySharp.CompilerServices
{
	using System;
	using System.Reflection;
	using Utilities;

	/// <summary>
	///     When applied to a method that can be affected by fault effects, indicates the method that implements the intended
	///     behavior of the method in the absence of any faults.
	/// </summary>
	[AttributeUsage(AttributeTargets.Method, AllowMultiple = false, Inherited = false)]
	public sealed class IntendedBehaviorAttribute : Attribute
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="methodName">The name of the behavior method.</param>
		public IntendedBehaviorAttribute(string methodName)
		{
			Requires.NotNull(methodName, () => methodName);
			MethodName = methodName;
		}

		/// <summary>
		///     Gets the name of the behavior method.
		/// </summary>
		public string MethodName { get; private set; }

		/// <summary>
		///     Gets the <see cref="MethodInfo" /> object representing the behavior method.
		/// </summary>
		/// <param name="type">The type that declares the behavior method.</param>
		public MethodInfo GetMethodInfo(Type type)
		{
			Requires.NotNull(type, () => type);

			var method = type.GetMethod(MethodName, BindingFlags.DeclaredOnly | BindingFlags.Instance | BindingFlags.NonPublic);
			Requires.That(method != null, "Unable to find method '{0}.{1}'.", type.FullName, MethodName);

			return method;
		}
	}
}