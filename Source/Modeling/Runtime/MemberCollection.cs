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
	using System.Linq;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Represents a collection of S# object members.
	/// </summary>
	/// <typeparam name="T">The actual type of the object members.</typeparam>
	public sealed class MemberCollection<T> : IEnumerable<T>
		where T : class
	{
		/// <summary>
		///     The members contained in the collection.
		/// </summary>
		private readonly T[] _members;

		/// <summary>
		///     The S# object the method collection belongs to.
		/// </summary>
		private readonly IMetadataObject _object;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="obj">The object the member collection belongs to.</param>
		/// <param name="members">The members that should be contained in the collection.</param>
		internal MemberCollection(IMetadataObject obj, IEnumerable<T> members)
		{
			Requires.NotNull(members, () => members);

			_object = obj;
			_members = members.ToArray();
		}

		/// <summary>
		///     Gets the metadata of the declaring object.
		/// </summary>
		public ObjectMetadata DeclaringObject
		{
			get { return _object.Metadata; }
		}

		/// <summary>
		///     Gets the member at the zero-based <paramref name="index" /> within the collection.
		/// </summary>
		/// <param name="index">The index of the member that should be returned.</param>
		public T this[int index]
		{
			get { return _members[index]; }
		}

		/// <summary>
		///     Gets the number of members in the collection.
		/// </summary>
		public int Length
		{
			get { return _members.Length; }
		}

		/// <summary>
		///     Returns an enumerator that iterates through the collection.
		/// </summary>
		IEnumerator<T> IEnumerable<T>.GetEnumerator()
		{
			foreach (var method in _members)
				yield return method;
		}

		/// <summary>
		///     Returns an enumerator that iterates through the collection.
		/// </summary>
		IEnumerator IEnumerable.GetEnumerator()
		{
			foreach (var method in _members)
				yield return method;
		}

		/// <summary>
		///     Executes <paramref name="action" /> for all members of the collection.
		/// </summary>
		/// <param name="action">The action that should be executed for each member of the collection.</param>
		internal void ForEach(Action<T> action)
		{
			Requires.NotNull(action, () => action);

			foreach (var member in _members)
				action(member);
		}
	}
}