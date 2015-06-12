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
	using System.Collections;
	using System.Collections.Generic;
	using System.Collections.Immutable;
	using Utilities;

	/// <summary>
	///     Represents a collection of <see cref="ComponentMethodInfo" /> instances.
	/// </summary>
	/// <typeparam name="T">The actual type of the <see cref="ComponentMethodInfo" /> instances.</typeparam>
	public sealed class ComponentMethodCollection<T> : IEnumerable<T>
		where T : ComponentMethodInfo
	{
		private ImmutableArray<T> _methods;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="methods">The methods that should be contained in the collection.</param>
		internal ComponentMethodCollection(IEnumerable<T> methods)
		{
			Requires.NotNull(methods, () => methods);
			_methods = methods.ToImmutableArray();
		}

		/// <summary>
		///     Gets the method at the zero-based <paramref name="index" /> within the collection.
		/// </summary>
		/// <param name="index">The index of the method that should be returned.</param>
		public T this[int index]
		{
			get { return _methods[index]; }
		}

		/// <summary>
		///     Gets the number of methods in the collection.
		/// </summary>
		public int Length
		{
			get { return _methods.Length; }
		}

		/// <summary>
		///     Returns an enumerator that iterates through the collection.
		/// </summary>
		IEnumerator<T> IEnumerable<T>.GetEnumerator()
		{
			foreach (var method in _methods)
				yield return method;
		}

		/// <summary>
		///     Returns an enumerator that iterates through the collection.
		/// </summary>
		IEnumerator IEnumerable.GetEnumerator()
		{
			foreach (var method in _methods)
				yield return method;
		}

		/// <summary>
		///     Returns an enumerator that iterates through the collection.
		/// </summary>
		public ImmutableArray<T>.Enumerator GetEnumerator()
		{
			return _methods.GetEnumerator();
		}
	}
}