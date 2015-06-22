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
	using Runtime;
	using Runtime.Statements;
	using Utilities;

	/// <summary>
	///     When applied to a S# method, indicates the name of the method that creates the <see cref="Statement" /> representing the
	///     method's body.
	/// </summary>
	[AttributeUsage(AttributeTargets.Method, AllowMultiple = false, Inherited = false)]
	public sealed class MethodBodyMetadataAttribute : Attribute
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="methodName">The name of the method that creates the method body metadata.</param>
		public MethodBodyMetadataAttribute(string methodName)
		{
			Requires.NotNullOrWhitespace(methodName, () => methodName);
			MethodName = methodName;
		}

		/// <summary>
		///     Gets the name of the method that creates the method body metadata.
		/// </summary>
		public string MethodName { get; private set; }

		/// <summary>
		///     Gets the <see cref="Statement" /> representing the <paramref name="method" />'s body.
		/// </summary>
		/// <param name="obj">The object the method body should be returned for.</param>
		/// <param name="method">The method the method body should be returned for.</param>
		public MethodBodyMetadata GetMethodBody(object obj, MethodInfo method)
		{
			Requires.NotNull(obj, () => obj);
			Requires.NotNull(method, () => method);

			var attribute = method.GetCustomAttribute<MethodBodyMetadataAttribute>();
			Requires.That(attribute != null, "Expected the method to be marked with an instance of '{0}'.", GetType().FullName);

			var bodyMethod = method.DeclaringType.GetMethod(MethodName, BindingFlags.Instance | BindingFlags.NonPublic);

			Requires.That(bodyMethod != null, "Unable to find the method body initialization method of method '{0}' declared by '{1}'.",
				method, method.DeclaringType.FullName);

			Requires.That(bodyMethod.GetParameters().Length == 0, "Expected no parameters on method '{0}' declared by '{1}'.",
				method, method.DeclaringType.FullName);

			Requires.That(bodyMethod.ReturnType == typeof(MethodBodyMetadata), "Expected method '{0}' declared by '{1}' to return a '{2}'.",
				method, method.DeclaringType.FullName, typeof(MethodBodyMetadata).FullName);

			return (MethodBodyMetadata)bodyMethod.Invoke(obj, null);
		}
	}
}