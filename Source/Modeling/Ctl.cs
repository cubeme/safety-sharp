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
	///     Provides factory methods for the construction of computation tree logic formulas.
	/// </summary>
	public static class Ctl
	{
		/// <summary>
		///     Gets a <see cref="CtlOperatorFactory" /> instance that provides methods for the application of CTL operators that
		///     operate on all paths of a subtree of a computation tree.
		/// </summary>
		public static CtlOperatorFactory AllPaths
		{
			get { throw new NotSupportedException(); }
		}

		/// <summary>
		///     Gets a <see cref="CtlOperatorFactory" /> instance that provides methods for the application of CTL operators that
		///     require the existence of a certain path within the subtree of a computation tree.
		/// </summary>
		public static CtlOperatorFactory ExistsPath
		{
			get { throw new NotSupportedException(); }
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that evaluates <paramref name="expression" /> within a system state.
		/// </summary>
		/// <param name="expression">The expression that should be evaluated.</param>
		public static CtlFormula StateExpression(Expression<Func<bool>> expression)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that evaluates <paramref name="expression" /> within a system state.
		/// </summary>
		/// <param name="expression">[LiftExpression] The expression that should be evaluated.</param>
		public static CtlFormula StateExpression([LiftExpression] bool expression)
		{
			throw new NotSupportedException();
		}
	}
}