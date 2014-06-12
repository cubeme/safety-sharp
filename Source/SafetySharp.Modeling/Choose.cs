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

namespace SafetySharp.Modeling
{
	using System;

	/// <summary>
	/// 
	/// </summary>
	public static class Choose
	{
		/// <summary>
		/// 
		/// </summary>
		/// <typeparam name="T"></typeparam>
		/// <returns></returns>
		public static T Literal<T>()
			where T : struct, IComparable, IFormattable, IConvertible
		{
			throw new NotSupportedException();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public static bool Boolean()
		{
			throw new NotSupportedException();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="value1"></param>
		/// <param name="value2"></param>
		/// <param name="values"></param>
		/// <returns></returns>
		public static int Value(int value1, int value2, params int[] values)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="value1"></param>
		/// <param name="value2"></param>
		/// <param name="values"></param>
		/// <returns></returns>
		public static decimal Value(decimal value1, decimal value2, params decimal[] values)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="inclusiveLowerBound"></param>
		/// <param name="inclusiveUpperBound"></param>
		/// <returns></returns>
		public static int FromRange(int inclusiveLowerBound, int inclusiveUpperBound)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="inclusiveLowerBound"></param>
		/// <param name="inclusiveUpperBound"></param>
		/// <returns></returns>
		public static decimal FromRange(decimal inclusiveLowerBound, decimal inclusiveUpperBound)
		{
			throw new NotSupportedException();
		}
	}
}