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

namespace SafetySharp.Formulas
{
	using System;
	using System.Collections.Generic;
	using System.Collections.Immutable;
	using System.Runtime.CompilerServices;
	using Metamodel.Configurations;
	using Metamodel.Expressions;
	using Utilities;

	/// <summary>
	///     Resolves the corresponding <see cref="FieldConfiguration" />s for all <see cref="FieldAccessExpression" />s contained in
	///     a <see cref="Formula" />.
	/// </summary>
	internal class FormulaResolver
	{
		/// <summary>
		///     The empty formula resolver that cannot resolve any references.
		/// </summary>
		internal static readonly FormulaResolver Empty = new FormulaResolver
		{
			_map = ImmutableDictionary.Create<FieldAccessExpression, FieldConfiguration>(new FieldAccessComparer())
		};

		/// <summary>
		///     Maps references of field declarations to component configurations.
		/// </summary>
		private ImmutableDictionary<FieldAccessExpression, FieldConfiguration> _map;

		/// <summary>
		///     Initializes a new instance of the <see cref="FormulaResolver" /> type.
		/// </summary>
		private FormulaResolver()
		{
		}

		/// <summary>
		///     Resolves the <paramref name="fieldAccessExpression" /> to the actual <see cref="FieldConfiguration" /> instance
		///     referenced by a formula.
		/// </summary>
		/// <param name="fieldAccessExpression">The field access expression that should be resolved.</param>
		public FieldConfiguration Resolve(FieldAccessExpression fieldAccessExpression)
		{
			Argument.NotNull(fieldAccessExpression, () => fieldAccessExpression);
			Argument.Satisfies(_map.ContainsKey(fieldAccessExpression), () => fieldAccessExpression, "The given expression is unknown.");

			return _map[fieldAccessExpression];
		}

		/// <summary>
		///     Creates a copy of the <see cref="FormulaResolver" /> that can resolve <paramref name="fieldAccessExpression" /> to
		///     <paramref name="fieldConfiguration" />.
		/// </summary>
		/// <param name="fieldAccessExpression">The field access expression that should be added to the resolver.</param>
		/// <param name="fieldConfiguration">The field configuration that <paramref name="fieldAccessExpression" /> refers to.</param>
		internal FormulaResolver With(FieldAccessExpression fieldAccessExpression, FieldConfiguration fieldConfiguration)
		{
			Argument.NotNull(fieldAccessExpression, () => fieldAccessExpression);
			Argument.NotNull(fieldConfiguration, () => fieldConfiguration);
			Argument.Satisfies(!_map.ContainsKey(fieldAccessExpression), () => fieldAccessExpression,
							   "The given reference has already been added to the resolver.");

			return new FormulaResolver { _map = _map.Add(fieldAccessExpression, fieldConfiguration) };
		}

		/// <summary>
		///     For the formula resolver, we actually need reference equality instead of value equality for field access expressions.
		/// </summary>
		private class FieldAccessComparer : IEqualityComparer<FieldAccessExpression>
		{
			/// <summary>
			///     Checks whether <paramref name="left" /> and <paramref name="right" /> are equal.
			/// </summary>
			/// <param name="left">The element on the left hand side of the equality operator.</param>
			/// <param name="right">The element on the right hand side of the equality operator.</param>
			public bool Equals(FieldAccessExpression left, FieldAccessExpression right)
			{
				return ReferenceEquals(left, right);
			}

			/// <summary>
			///     Gets the hash code of <paramref name="expression" /> for our notion of equality.
			/// </summary>
			/// <param name="expression">The expression the hash code should be returned for.</param>
			public int GetHashCode(FieldAccessExpression expression)
			{
				return RuntimeHelpers.GetHashCode(expression);
			}
		}
	}
}