// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

namespace SafetySharp.Metamodel
{
	using System;

	public struct Reference<T>
		where T : MetamodelElement
	{
		/// <summary>
		///     The slot that identifies the referenced element.
		/// </summary>
		private readonly int _slot;

		/// <summary>
		///     Initializes a new instance of the <see cref="Reference{T}" /> type.
		/// </summary>
		/// <param name="slot">The slot that identifies the referenced element.</param>
		public Reference(int slot)
		{
			_slot = slot;
		}

		/// <summary>
		///     Determines whether <paramref name="other" /> is equal to the current instance.
		/// </summary>
		/// <param name="other">The <see cref="Identifier" /> to compare with the current instance.</param>
		/// <returns>
		///     <c>true</c> if <paramref name="other" /> is equal to the current instance; otherwise, <c>false</c>.
		/// </returns>
		public bool Equals(Reference<T> other)
		{
			return _slot == other._slot;
		}

		/// <summary>
		///     Determines whether <paramref name="obj" /> is equal to the current instance.
		/// </summary>
		/// <param name="obj">The object to compare with the current instance.</param>
		/// <returns>
		///     <c>true</c> if <paramref name="obj" /> is equal to the current instance; otherwise, <c>false</c>.
		/// </returns>
		public override bool Equals(object obj)
		{
			if (ReferenceEquals(null, obj))
				return false;

			return obj is Reference<T> && Equals((Reference<T>)obj);
		}

		/// <summary>
		///     Gets the hash code for the current instance.
		/// </summary>
		public override int GetHashCode()
		{
			return _slot;
		}

		/// <summary>
		///     Checks whether <paramref name="left" /> and <paramref name="right" /> are equal.
		/// </summary>
		/// <param name="left">The element on the left hand side of the equality operator.</param>
		/// <param name="right">The element on the right hand side of the equality operator.</param>
		public static bool operator ==(Reference<T> left, Reference<T> right)
		{
			return left.Equals(right);
		}

		/// <summary>
		///     Checks whether <paramref name="left" /> and <paramref name="right" /> are not equal.
		/// </summary>
		/// <param name="left">The element on the left hand side of the inequality operator.</param>
		/// <param name="right">The element on the right hand side of the inequality operator.</param>
		public static bool operator !=(Reference<T> left, Reference<T> right)
		{
			return !left.Equals(right);
		}
	}
}