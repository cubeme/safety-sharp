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

	/// <summary>
	///     Represents a reference to a metamodel element that can be resolved by a <see cref="MetamodelResolver" />.
	/// </summary>
	/// <typeparam name="T">The type of the referenced metamodel element.</typeparam>
	public class Reference<T>
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
	}
}