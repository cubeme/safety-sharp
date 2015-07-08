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

namespace SafetySharp.Modeling
{
	using System;
	using Utilities;

	/// <summary>
	///     Represents a state of a <see cref="Component" />'s state machine.
	/// </summary>
	public struct State : IEquatable<State>
	{
		/// <summary>
		///     The enum value of the state.
		/// </summary>
		private readonly object _value;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="value">The enum value of the state.</param>
		internal State(object value)
		{
			_value = value;
		}

		/// <summary>
		///     Indicates whether the current state is equal to <paramref name="state" />.
		/// </summary>
		/// <param name="state">The state to compare with this state.</param>
		public bool Equals(State state)
		{
			return Equals(_value, state._value);
		}

		/// <summary>
		///     Indicates whether the current state is equal to <paramref name="state" />.
		/// </summary>
		/// <param name="state">The state to compare with this state.</param>
		public override bool Equals(object state)
		{
			if (ReferenceEquals(null, state))
				return false;

			return state is State && Equals((State)state);
		}

		/// <summary>
		///     Returns the hash code for this instance.
		/// </summary>
		public override int GetHashCode()
		{
			return (_value != null ? _value.GetHashCode() : 0);
		}

		/// <summary>
		///     Casts the state to type <typeparamref name="T" />.
		/// </summary>
		/// <typeparam name="T">The type the state should be cast to.</typeparam>
		public T As<T>()
		{
			Requires.That(_value != null, "No state has been set.");
			return (T)_value;
		}

		/// <summary>
		///     Indicates whether <paramref name="left" /> and <paramref name="right" /> are equal.
		/// </summary>
		/// <param name="left">The left state to compare.</param>
		/// <param name="right">The right state to compare.</param>
		public static bool operator ==(State left, State right)
		{
			return left._value.Equals(right._value);
		}

		/// <summary>
		///     Indicates whether <paramref name="left" /> and <paramref name="right" /> are not equal.
		/// </summary>
		/// <param name="left">The left state to compare.</param>
		/// <param name="right">The right state to compare.</param>
		public static bool operator !=(State left, State right)
		{
			return !left._value.Equals(right._value);
		}

		/// <summary>
		///     Indicates whether <paramref name="left" /> and <paramref name="right" /> are equal.
		/// </summary>
		/// <param name="left">The left state to compare.</param>
		/// <param name="right">The right state to compare.</param>
		public static bool operator ==(State left, object right)
		{
			return left._value.Equals(right);
		}

		/// <summary>
		///     Indicates whether <paramref name="left" /> and <paramref name="right" /> are not equal.
		/// </summary>
		/// <param name="left">The left state to compare.</param>
		/// <param name="right">The right state to compare.</param>
		public static bool operator !=(State left, object right)
		{
			return !left._value.Equals(right);
		}

		/// <summary>
		///     Indicates whether <paramref name="left" /> and <paramref name="right" /> are equal.
		/// </summary>
		/// <param name="left">The left state to compare.</param>
		/// <param name="right">The right state to compare.</param>
		public static bool operator ==(object left, State right)
		{
			return left.Equals(right._value);
		}

		/// <summary>
		///     Indicates whether <paramref name="left" /> and <paramref name="right" /> are not equal.
		/// </summary>
		/// <param name="left">The left state to compare.</param>
		/// <param name="right">The right state to compare.</param>
		public static bool operator !=(object left, State right)
		{
			return !left.Equals(right._value);
		}
	}
}