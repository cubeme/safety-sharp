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
	using Utilities;

	/// <summary>
	///     Represents a position within a source file, specified by a zero-based line index and a zero-based character index within
	///     the line.
	/// </summary>
	public struct LinePosition : IEquatable<LinePosition>
	{
		/// <summary>
		///     Initializes a new instance of the <see cref="LinePosition" /> type.
		/// </summary>
		/// <param name="line">The line of the line position. The index of the first line in a file is 0.</param>
		/// <param name="character">The character position in the line. The first character of the line has position 0.</param>
		/// <exception cref="ArgumentException">Thrown if <paramref name="line" /> or <paramref name="character" /> is less than 0.</exception>
		public LinePosition(int line, int character)
			: this()
		{
			Assert.ArgumentSatisfies(line >= 0, () => line);
			Assert.ArgumentSatisfies(character >= 0, () => character);

			Line = line;
			Character = character;
		}

		/// <summary>
		///     Gets the line of the line position. The index of the first line in a file is 0.
		/// </summary>
		public int Line { get; private set; }

		/// <summary>
		///     Gets the character position in the line. The first character of the line has position 0.
		/// </summary>
		public int Character { get; private set; }

		/// <summary>
		///     Indicates whether the current object is equal to another object of the same type.
		/// </summary>
		/// <param name="other">An object to compare with this object.</param>
		/// <returns>
		///     <c>true</c> if the current object is equal to the <paramref name="other" /> parameter; otherwise, <c>false</c>.
		/// </returns>
		public bool Equals(LinePosition other)
		{
			return Line == other.Line && Character == other.Character;
		}

		/// <summary>
		///     Indicates whether this instance and <paramref name="obj" /> are equal.
		/// </summary>
		/// <param name="obj">Another object to compare to. </param>
		/// <returns>
		///     <c>true</c> if <paramref name="obj" /> and this instance are the same type and represent the same value; otherwise,
		///     <c>false</c>.
		/// </returns>
		public override bool Equals(object obj)
		{
			if (ReferenceEquals(null, obj))
				return false;

			return obj is LinePosition && Equals((LinePosition)obj);
		}

		/// <summary>
		///     Returns the hash code for this instance.
		/// </summary>
		/// <returns>
		///     A 32-bit signed integer that is the hash code for this instance.
		/// </returns>
		public override int GetHashCode()
		{
			unchecked
			{
				return (Line * 397) ^ Character;
			}
		}

		/// <summary>
		///     Determines whether two specified line positions have the same value.
		/// </summary>
		/// <param name="left">The first line position that should be compared.</param>
		/// <param name="right">The second line position that should be compared.</param>
		/// <returns>
		///     <c>true</c> if the value of <paramref name="left" /> is the same as the value of <paramref name="right" />;
		///     otherwise, <c>false</c>.
		/// </returns>
		public static bool operator ==(LinePosition left, LinePosition right)
		{
			return left.Equals(right);
		}

		/// <summary>
		///     Determines whether two specified line positions have different values.
		/// </summary>
		/// <param name="left">The first line position that should be compared.</param>
		/// <param name="right">The second line position that should be compared.</param>
		/// <returns>
		///     <c>true</c> if the value of <paramref name="left" /> is the different from the value of <paramref name="right" />;
		///     otherwise, <c>false</c>.
		/// </returns>
		public static bool operator !=(LinePosition left, LinePosition right)
		{
			return !left.Equals(right);
		}
	}
}