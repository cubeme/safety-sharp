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

namespace SafetySharp.Utilities
{
	using System;
	using System.Collections;
	using System.Diagnostics;
	using System.Linq.Expressions;

	/// <summary>
	///     Defines a set of helper functions that should be used to assert preconditions of functions, class invariants, etc.
	/// </summary>
	public static class Assert
	{
		/// <summary>
		///     Throws an <see cref="ArgumentNullException" /> if <paramref name="argument" /> of reference type
		///     <typeparamref name="T" /> is <c>null</c>.
		/// </summary>
		/// <typeparam name="T">The type of the argument that should be checked.</typeparam>
		/// <param name="argument">The actual argument whose value should be checked.</param>
		/// <param name="argumentName">
		///     A lambda expression of the form <c>() => argument</c> that is used to deduce the name of the
		///     argument as it appears in the source code.
		/// </param>
		/// <exception cref="ArgumentNullException">
		///     Thrown if the value of <paramref name="argument" /> or <paramref name="argumentName" /> is <c>null</c>.
		/// </exception>
		[Conditional("DEBUG"), DebuggerHidden]
		public static void ArgumentNotNull<T>(T argument, Expression<Func<T>> argumentName)
			where T : class
		{
			if (argumentName == null)
				throw new ArgumentNullException("argumentName");

			if (argument == null)
				throw new ArgumentNullException(GetArgumentName(argumentName));
		}

		/// <summary>
		///     Throws an <see cref="ArgumentNullException" /> if <paramref name="argument" /> is <c>null</c>. If
		///     <paramref name="argument" /> is empty or consists of whitespace only, an <see cref="ArgumentException" /> is thrown.
		/// </summary>
		/// <param name="argument">The actual argument whose value should be checked.</param>
		/// <param name="argumentName">
		///     A lambda expression of the form <c>() => argument</c> that is used to deduce the name of the
		///     argument as it appears in the source code.
		/// </param>
		/// <exception cref="ArgumentNullException">
		///     Thrown if the value of <paramref name="argument" /> or <paramref name="argumentName" /> is <c>null</c>.
		/// </exception>
		/// <exception cref="ArgumentException">
		///     Thrown if the value of <paramref name="argument" /> is empty or consists of whitespace only.
		/// </exception>
		[Conditional("DEBUG"), DebuggerHidden]
		public static void ArgumentNotNullOrWhitespace(string argument, Expression<Func<string>> argumentName)
		{
			ArgumentNotNull(argumentName, () => argumentName);

			if (argument == null)
				throw new ArgumentNullException(GetArgumentName(argumentName));

			if (String.IsNullOrWhiteSpace(argument))
				throw new ArgumentException("The argument cannot be empty or consist of whitespace only.", GetArgumentName(argumentName));
		}

		/// <summary>
		///     Throws an <see cref="ArgumentOutOfRangeException" /> if <paramref name="argument" /> of enumeration type
		///     <typeparamref name="TEnum" /> is outside the range of valid enumeration literals. This method cannot be used to check
		///     enumeration literals if the <see cref="FlagsAttribute" /> is set on <typeparamref name="TEnum" />.
		/// </summary>
		/// <typeparam name="TEnum">The type of the enumeration argument that should be checked.</typeparam>
		/// <param name="argument">The actual enumeration value that should be checked.</param>
		/// <param name="argumentName">
		///     A lambda expression of the form <c>() => argument</c> that is used to deduce the name of the
		///     argument as it appears in the source code.
		/// </param>
		/// <exception cref="ArgumentNullException">Thrown if <paramref name="argumentName" /> is <c>null</c>.</exception>
		/// <exception cref="ArgumentException">Thrown if <typeparamref name="TEnum" /> is not an enumeration type.</exception>
		/// <exception cref="ArgumentOutOfRangeException">
		///     Thrown if the value of <paramref name="argument" /> is outside the range of valid enumeration literals.
		/// </exception>
		[Conditional("DEBUG"), DebuggerHidden]
		public static void ArgumentInRange<TEnum>(TEnum argument, Expression<Func<TEnum>> argumentName)
			where TEnum : struct
		{
			ArgumentNotNull(argumentName, () => argumentName);

			if (!typeof(TEnum).IsEnum)
				throw new ArgumentException(String.Format("'{0}' is not an enumeration type.", typeof(TEnum).FullName), GetArgumentName(argumentName));

			if (!Enum.IsDefined(typeof(TEnum), argument))
				throw new ArgumentOutOfRangeException(GetArgumentName(argumentName), argument, "Enumeration parameter is out of range.");
		}

		/// <summary>
		///     Throws an <see cref="ArgumentOutOfRangeException" /> if the value of <paramref name="argument" /> of
		///     <see cref="IComparable" /> type <typeparamref name="T" /> is outside the range defined by the inclusive
		///     <paramref name="lowerBound" /> and the exclusive <paramref name="upperBound" />.
		/// </summary>
		/// <typeparam name="T">The type of the value to check.</typeparam>
		/// <param name="argument">The actual value that should be checked.</param>
		/// <param name="argumentName">
		///     A lambda expression of the form <c>() => argument</c> that is used to deduce the name of the
		///     argument as it appears in the source code.
		/// </param>
		/// <param name="lowerBound">The inclusive lower bound of the range.</param>
		/// <param name="upperBound">The exclusive upper bound of the range.</param>
		/// <exception cref="ArgumentNullException">Thrown if <paramref name="argumentName" /> is <c>null</c>.</exception>
		/// <exception cref="ArgumentException">
		///     Thrown if <paramref name="lowerBound" /> does not precede <paramref name="upperBound" />.
		/// </exception>
		/// <exception cref="ArgumentOutOfRangeException">
		///     Thrown if the value of <paramref name="argument" /> precedes <paramref name="lowerBound" /> or is
		///     the same as or exceeds <paramref name="upperBound" />.
		/// </exception>
		[Conditional("DEBUG"), DebuggerHidden]
		public static void ArgumentInRange<T>(T argument, Expression<Func<T>> argumentName, T lowerBound, T upperBound)
			where T : IComparable<T>
		{
			ArgumentNotNull(argumentName, () => argumentName);
			ArgumentSatisfies(lowerBound.CompareTo(upperBound) <= 0, () => lowerBound,
							  "lowerBound '{0}' does not precede upperBound '{1}'.", lowerBound, upperBound);

			if (argument.CompareTo(lowerBound) < 0)
				throw new ArgumentOutOfRangeException(GetArgumentName(argumentName), argument, "Lower bound range violation.");

			if (argument.CompareTo(upperBound) >= 0)
				throw new ArgumentOutOfRangeException(GetArgumentName(argumentName), argument, "Upper bound range violation.");
		}

		/// <summary>
		///     Throws an <see cref="ArgumentOutOfRangeException" /> if the value of <paramref name="indexArgument" />
		///     falls outside the range of valid indices for <paramref name="collection" />.
		/// </summary>
		/// <param name="indexArgument">The actual index that should be checked.</param>
		/// <param name="argumentName">
		///     A lambda expression of the form <c>() => argument</c> that is used to deduce the name of the
		///     index argument as it appears in the source code.
		/// </param>
		/// <param name="collection">The collection defining the range of valid indices.</param>
		/// <exception cref="ArgumentNullException">
		///     Thrown if the value of <paramref name="argumentName" /> or <paramref name="collection" /> is <c>null</c>.
		/// </exception>
		/// <exception cref="ArgumentOutOfRangeException">
		///     Thrown if the value of <paramref name="indexArgument" /> is smaller than 0 or exceeds <c>collection.Count</c>.
		/// </exception>
		[Conditional("DEBUG"), DebuggerHidden]
		public static void ArgumentInRange(int indexArgument, Expression<Func<int>> argumentName, ICollection collection)
		{
			ArgumentNotNull(argumentName, () => argumentName);
			ArgumentNotNull(collection, () => collection);
			ArgumentInRange(indexArgument, argumentName, 0, collection.Count);
		}

		/// <summary>
		///     Throws an <see cref="ArgumentException" /> if <paramref name="condition" /> is <c>false</c>.
		/// </summary>
		/// <typeparam name="T">The type of the argument that is checked.</typeparam>
		/// <param name="condition">The condition that, if <c>false</c>, causes the exception to be raised.</param>
		/// <param name="argumentName">
		///     A lambda expression of the form <c>() => argument</c> that is used to deduce the name of the
		///     index argument as it appears in the source code.
		/// </param>
		/// <param name="message">An optional message providing further details about the assertion.</param>
		/// <param name="parameters">The parameters for formatting <paramref name="message"/>.</param>
		/// <exception cref="ArgumentNullException">Thrown if <paramref name="argumentName" /> is <c>null</c>.</exception>
		/// <exception cref="ArgumentException">Thrown if <paramref name="condition" /> is <c>false</c>.</exception>
		[Conditional("DEBUG"), DebuggerHidden, StringFormatMethod("message")]
		public static void ArgumentSatisfies<T>(bool condition, Expression<Func<T>> argumentName,
												string message = null, params object[] parameters)
		{
			ArgumentNotNull(argumentName, () => argumentName);

			if (condition)
				return;

			message = message == null ? "An assertion violation occurred." : String.Format(message, parameters);
			throw new ArgumentException(message, GetArgumentName(argumentName));
		}

		/// <summary>
		///     Throws an <see cref="ArgumentException" /> if <paramref name="argument" /> is not of type
		///     <typeparamref name="T" />.
		/// </summary>
		/// <typeparam name="T">The desired type of <paramref name="argument" />.</typeparam>
		/// <param name="argument">The value whose type should be checked.</param>
		/// <param name="argumentName">
		///     A lambda expression of the form <c>() => argument</c> that is used to deduce the name of the
		///     index argument as it appears in the source code.
		/// </param>
		/// <param name="message">An optional message providing further details about the assertion.</param>
		/// <param name="parameters">The parameters for formatting <paramref name="message"/>.</param>
		/// <exception cref="ArgumentNullException">
		///     Thrown if <paramref name="argument" /> or <paramref name="argumentName" /> is <c>null</c>.
		/// </exception>
		/// <exception cref="ArgumentException">Thrown if <paramref name="argument" /> is not of type <typeparamref name="T" />.</exception>
		[Conditional("DEBUG"), DebuggerHidden, StringFormatMethod("message")]
		public static void ArgumentOfType<T>(object argument, Expression<Func<object>> argumentName,
											 string message = null, params object[] parameters)
			where T : class
		{
			ArgumentNotNull(argument, () => argument);
			ArgumentNotNull(argumentName, () => argumentName);

			if (argument is T)
				return;

			message = message == null
				? String.Format("Expected an instance of type '{0}' but found an instance of type '{1}'.",
								typeof(T).FullName, argument.GetType().FullName)
				: String.Format(message, parameters);

			throw new ArgumentException(message, GetArgumentName(argumentName));
		}

		/// <summary>
		///     Throws an <see cref="InvalidOperationException" /> if <paramref name="obj" /> is not <c>null</c>.
		/// </summary>
		/// <typeparam name="T">The type of the object that should be checked.</typeparam>
		/// <param name="obj">The object that should be checked.</param>
		/// <param name="message">An optional message providing further details about the assertion.</param>
		/// <param name="parameters">The parameters for formatting <paramref name="message"/>.</param>
		/// <exception cref="InvalidOperationException">Thrown if <paramref name="obj" /> is not <c>null</c>.</exception>
		[Conditional("DEBUG"), DebuggerHidden, StringFormatMethod("message")]
		public static void IsNull<T>(T obj, string message = null, params object[] parameters)
			where T : class
		{
			if (obj == null)
				return;

			message = message == null ? "Expected 'null'." : String.Format(message, parameters);
			throw new InvalidOperationException(message);
		}

		/// <summary>
		///     Throws an <see cref="NullReferenceException" /> if <paramref name="obj" /> is <c>null</c>.
		/// </summary>
		/// <typeparam name="T">The type of the object that should be checked.</typeparam>
		/// <param name="obj">The object that should be checked.</param>
		/// <param name="message">An optional message providing further details about the assertion.</param>
		/// <param name="parameters">The parameters for formatting <paramref name="message"/>.</param>
		/// <exception cref="NullReferenceException">Thrown if <paramref name="obj" /> is <c>null</c>.</exception>
		[Conditional("DEBUG"), DebuggerHidden, StringFormatMethod("message")]
		public static void NotNull<T>(T obj, string message = null, params object[] parameters)
			where T : class
		{
			if (obj != null)
				return;

			message = message == null ? "Unexpected 'null'." : String.Format(message, parameters);
			throw new NullReferenceException(message);
		}

		/// <summary>
		///     Throws an <see cref="NullReferenceException" /> if <paramref name="s" /> is <c>null</c>. If
		///     <paramref name="s" /> is empty or consists of whitespace only, an <see cref="InvalidOperationException" /> is thrown.
		/// </summary>
		/// <param name="s">The string that should be checked.</param>
		/// <exception cref="NullReferenceException">Thrown if <paramref name="s" /> is <c>null</c>.</exception>
		/// <exception cref="InvalidOperationException">Thrown if <paramref name="s" /> is empty or consists of whitespace only.</exception>
		[Conditional("DEBUG"), DebuggerHidden]
		public static void NotNullOrWhitespace(string s)
		{
			if (s == null)
				throw new NullReferenceException("Expected a non-null 'String' instance.");

			if (String.IsNullOrWhiteSpace(s))
				throw new InvalidOperationException("The string cannot be empty or consist of whitespace only.");
		}

		/// <summary>
		///     Throws an <see cref="InvalidOperationException" /> if <paramref name="condition" /> is <c>false</c>.
		/// </summary>
		/// <param name="condition">The condition that, if <c>false</c>, causes the exception to be raised.</param>
		/// <param name="message">A message providing further details about the assertion.</param>
		/// <param name="parameters">The parameters for formatting <paramref name="message"/>.</param>
		[Conditional("DEBUG"), DebuggerHidden, StringFormatMethod("message")]
		public static void That(bool condition, string message, params object[] parameters)
		{
			ArgumentNotNullOrWhitespace(message, () => message);

			if (!condition)
				throw new InvalidOperationException(String.Format(message, parameters));
		}

		/// <summary>
		///     Throws an <see cref="InvalidOperationException" /> every time the method is invoked. This method is intended to be used
		///     in default cases of switch statements that should never be reached, for instance.
		/// </summary>
		/// <param name="message">An optional message providing further details about the assertion.</param>
		/// <param name="parameters">The parameters for formatting <paramref name="message"/>.</param>
		[Conditional("DEBUG"), DebuggerHidden, StringFormatMethod("message")]
		public static void NotReached(string message = null, params object[] parameters)
		{
			message = message == null ? "Control flow should not have reached this point." : String.Format(message, parameters);
			That(false, message);
		}

		/// <summary>
		///     Throws an <see cref="InvalidOperationException" /> if <paramref name="value" /> of enumeration type
		///     <typeparamref name="TEnum" /> is outside the range of valid enumeration literals. This method cannot be used to check
		///     enumeration literals if the <see cref="FlagsAttribute" /> is set on <typeparamref name="TEnum" />.
		/// </summary>
		/// <typeparam name="TEnum">The type of the enumeration value that should be checked.</typeparam>
		/// <param name="value">The actual enumeration value that should be checked.</param>
		/// <exception cref="InvalidOperationException">
		///     Thrown if <typeparamref name="TEnum" /> is not an enumeration type or if the value of <paramref name="value" /> is
		///     outside the range of valid enumeration literals.
		/// </exception>
		[Conditional("DEBUG"), DebuggerHidden]
		public static void InRange<TEnum>(TEnum value)
			where TEnum : struct
		{
			if (!typeof(TEnum).IsEnum)
				throw new InvalidOperationException(String.Format("'{0}' is not an enumeration type.", typeof(TEnum).FullName));

			if (!Enum.IsDefined(typeof(TEnum), value))
				throw new InvalidOperationException("Enumeration value is out of range.");
		}

		/// <summary>
		///     Throws an <see cref="InvalidOperationException" /> if <paramref name="value" /> of
		///     <see cref="IComparable" /> type <typeparamref name="T" /> is outside the range defined by the inclusive
		///     <paramref name="lowerBound" /> and the exclusive <paramref name="upperBound" />.
		/// </summary>
		/// <typeparam name="T">The type of the value to check.</typeparam>
		/// <param name="value">The actual value that should be checked.</param>
		/// <param name="lowerBound">The inclusive lower bound of the range.</param>
		/// <param name="upperBound">The exclusive upper bound of the range.</param>
		/// <exception cref="ArgumentException">
		///     Thrown if <paramref name="lowerBound" /> does not precede <paramref name="upperBound" />.
		/// </exception>
		/// <exception cref="InvalidOperationException">
		///     Thrown if the value of <paramref name="value" /> precedes <paramref name="lowerBound" /> or is
		///     the same as or exceeds <paramref name="upperBound" />.
		/// </exception>
		[Conditional("DEBUG"), DebuggerHidden]
		public static void InRange<T>(T value, T lowerBound, T upperBound)
			where T : IComparable<T>
		{
			ArgumentSatisfies(lowerBound.CompareTo(upperBound) <= 0, () => lowerBound,
							  "lowerBound '{0}' does not precede upperBound '{1}'.", lowerBound, upperBound);

			if (value.CompareTo(lowerBound) < 0)
				throw new InvalidOperationException(
					String.Format("Lower bound violation. Expected argument to lie between {0} and {1}.", lowerBound, upperBound));

			if (value.CompareTo(upperBound) >= 0)
				throw new InvalidOperationException(
					String.Format("Upper bound violation. Expected argument to lie between {0} and {1}.", lowerBound, upperBound));
		}

		/// <summary>
		///     Throws an <see cref="InvalidOperationException" /> if <paramref name="index" />
		///     falls outside the range of valid indices for <paramref name="collection" />.
		/// </summary>
		/// <param name="index">The actual index that should be checked.</param>
		/// <param name="collection">The collection defining the range of valid indices.</param>
		/// <exception cref="ArgumentNullException">Thrown if <paramref name="collection" /> is <c>null</c>.</exception>
		/// <exception cref="InvalidOperationException">
		///     Thrown if the value of <paramref name="index" /> is smaller than 0 or exceeds <c>collection.Count</c>.
		/// </exception>
		[Conditional("DEBUG"), DebuggerHidden]
		public static void InRange(int index, ICollection collection)
		{
			ArgumentNotNull(collection, () => collection);
			InRange(index, 0, collection.Count);
		}

		/// <summary>
		///     Retrieves the name of the argument referenced by the <paramref name="argumentName" /> expression. Expects
		///     <paramref name="argumentName" /> to be a lambda expression of the form <c>() => argument</c>.
		/// </summary>
		/// <param name="argumentName"></param>
		/// <returns>Returns the name of the member or local variable accessed by the expression.</returns>
		private static string GetArgumentName<T>(Expression<Func<T>> argumentName)
		{
			ArgumentOfType<MemberExpression>(argumentName, () => argumentName,
											 "Expected a lambda expression of the form '() => argument'.");

			return ((MemberExpression)argumentName.Body).Member.Name;
		}
	}
}