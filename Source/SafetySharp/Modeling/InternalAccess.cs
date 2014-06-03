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
	using Utilities;

	/// <summary>
	/// 
	/// </summary>
	/// <typeparam name="T"></typeparam>
	public sealed class InternalAccess<T> : IInternalAccess
	{
		private readonly IComponent _component;
		private readonly string _memberName;

		/// <summary>
		///     Initializes a new instance of the <see cref="InternalAccess{T}" /> type.
		/// </summary>
		internal InternalAccess(IComponent component, string memberName)
		{
			Argument.NotNull(component, () => component);
			Argument.NotNull(memberName, () => memberName);

			_component = component;
			_memberName = memberName;
		}

		/// <summary>
		/// 
		/// </summary>
		IComponent IInternalAccess.Component
		{
			get { return _component; }
		}

		/// <summary>
		/// 
		/// </summary>
		string IInternalAccess.MemberName
		{
			get { return _memberName; }
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="access"></param>
		/// <returns></returns>
		public static implicit operator T(InternalAccess<T> access)
		{
			throw new NotSupportedException();
		}
	}
}