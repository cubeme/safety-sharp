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

	/// <summary>
	///     Raised when a component is found in multiple locations of a component tree.
	/// </summary>
	public class SharedComponentsException : Exception
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="components">The shared components that were found in multiple locations of the component tree.</param>
		public SharedComponentsException(Component[] components)
			: base("One or more components have been found in multiple locations of the component tree. " +
				   "Check the 'Components' property of this exception instance for the shared component instances.")
		{
			Components = components;
		}

		/// <summary>
		///     Gets the component instances that were found in multiple locations of a component tree.
		/// </summary>
		public Component[] Components { get; private set; }
	}
}