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

	/// <summary>
	///     Provides methods for nondeterministic choices.
	/// </summary>
	public static class Choose
	{
		/// <summary>
		///     Returns one of the literal values of the enumeration type <typeparamref name="T" /> nondeterministically.
		/// </summary>
		/// <typeparam name="T">The type of the enumeration.</typeparam>
		public static T Literal<T>()
			where T : struct, IComparable, IFormattable, IConvertible
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a Boolean value nondeterministically.
		/// </summary>
		public static bool Boolean()
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a value found in <paramref name="values" /> nondeterministically.
		/// </summary>
		/// <param name="values">The values to choose from.</param>
		public static int Value(params int[] values)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a value found in <paramref name="values" /> nondeterministically.
		/// </summary>
		/// <param name="values">The values to choose from.</param>
		public static int Value(params double[] values)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a value within the range of <paramref name="inclusiveLowerBound" /> and <paramref name="inclusiveUpperBound" />
		///     nondeterministically.
		/// </summary>
		/// <param name="inclusiveLowerBound">The inclusive lower bound of the range to choose from.</param>
		/// <param name="inclusiveUpperBound">The inclusive upper bound of the range to choose from.</param>
		public static int FromRange(int inclusiveLowerBound, int inclusiveUpperBound)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a value within the range of <paramref name="inclusiveLowerBound" /> and <paramref name="inclusiveUpperBound" />
		///     nondeterministically.
		/// </summary>
		/// <param name="inclusiveLowerBound">The inclusive lower bound of the range to choose from.</param>
		/// <param name="inclusiveUpperBound">The inclusive upper bound of the range to choose from.</param>
		public static int FromRange(double inclusiveLowerBound, double inclusiveUpperBound)
		{
			throw new NotSupportedException();
		}
	}
}