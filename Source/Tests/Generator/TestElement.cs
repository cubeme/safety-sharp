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

namespace Tests.Generator
{
	using System;

	/// <summary>
	///     Represents a metamodel element. Metamodel elements are organized as semantically enriched syntax trees.
	/// </summary>
	internal abstract class TestElement
	{
		/// <summary>
		///     Accepts <paramref name="visitor" />, calling the type-specific visit method.
		/// </summary>
		/// <param name="visitor">The visitor the type-specific visit method should be invoked on.</param>
		public abstract void Accept(TestVisitor visitor);

		/// <summary>
		///     Accepts <paramref name="visitor" />, calling the type-specific visit method.
		/// </summary>
		/// <typeparam name="TResult">The type of the value returned by <paramref name="visitor" />.</typeparam>
		/// <param name="visitor">The visitor the type-specific visit method should be invoked on.</param>
		public abstract TResult Accept<TResult>(TestVisitor<TResult> visitor);

		/// <summary>
		///     Determines whether <paramref name="other" /> is equal to the current instance.
		/// </summary>
		/// <param name="other">The <see cref="TestElement" /> to compare with the current instance.</param>
		/// <returns>
		///     <c>true</c> if <paramref name="other" /> is equal to the current instance; otherwise, <c>false</c>.
		/// </returns>
		public abstract bool Equals(TestElement other);
	}
}