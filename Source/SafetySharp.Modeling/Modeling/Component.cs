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
	using System.Linq.Expressions;

	/// <summary>
	/// 
	/// </summary>
	public abstract class Component : IComponent
	{
		/// <summary>
		/// 
		/// </summary>
		protected Component()
		{
		}

		/// <summary>
		/// 
		/// </summary>
		/// <typeparam name="T"></typeparam>
		/// <returns></returns>
		protected static T Choose<T>()
			where T : struct
		{
			return default(T);
		}

		/// <summary>
		/// 
		/// </summary>
		/// <typeparam name="T"></typeparam>
		/// <param name="value1"></param>
		/// <param name="value2"></param>
		/// <param name="values"></param>
		/// <returns></returns>
		protected static T Choose<T>(T value1, T value2, params T[] values)
		{
			return default(T);
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="inclusiveLowerBound"></param>
		/// <param name="inclusiveUpperBound"></param>
		/// <returns></returns>
		protected static int ChooseFromRange(int inclusiveLowerBound, int inclusiveUpperBound)
		{
			return 0;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="inclusiveLowerBound"></param>
		/// <param name="inclusiveUpperBound"></param>
		/// <returns></returns>
		protected static decimal ChooseFromRange(decimal inclusiveLowerBound, decimal inclusiveUpperBound)
		{
			return 0;
		}

		/// <summary>
		/// 
		/// </summary>
		protected virtual void Update()
		{
		}

		/// <summary>
		///     Adds metadata about a field of the component to the <see cref="Component" /> instance.
		/// </summary>
		/// <param name="field">An expression of the form <c>() => field</c> that referes to a field of the component.</param>
		/// <param name="initialValues">The initial values of the field.</param>
		protected void SetInitialValues<T>(Expression<Func<T>> field, params T[] initialValues)
		{
		}
	}
}