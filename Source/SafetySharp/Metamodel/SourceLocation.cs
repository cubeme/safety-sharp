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
	///     Represents a location within a source file.
	/// </summary>
	public struct SourceLocation : IEquatable<SourceLocation>
	{
		/// <summary>
		///     Initializes a new instance of the <see cref="SourceLocation" /> type.
		/// </summary>
		/// <param name="file">The path of the file the source location refers to.</param>
		/// <param name="start">The start position of the source location.</param>
		/// <param name="end">The end position of the source location.</param>
		/// <exception cref="ArgumentNullException">Thrown if <paramref name="file" /> is null.</exception>
		/// <exception cref="ArgumentException">Thrown if <paramref name="file" /> consists of whitespace only.</exception>
		public SourceLocation(string file, LinePosition start, LinePosition end)
			: this()
		{
			Assert.ArgumentNotNullOrWhitespace(file, () => file);

			File = file;
			Start = start;
			End = end;
		}

		/// <summary>
		///     Gets the path of the file the source location refers to.
		/// </summary>
		public string File { get; private set; }

		/// <summary>
		///     Gets the start position of the source location.
		/// </summary>
		public LinePosition Start { get; private set; }

		/// <summary>
		///     Gets the end position of the source location.
		/// </summary>
		public LinePosition End { get; private set; }

		/// <summary>
		///     Indicates whether the current object is equal to another object of the same type.
		/// </summary>
		/// <param name="other">An object to compare with this object.</param>
		/// <returns>
		///     <c>true</c> if the current object is equal to the <paramref name="other" /> parameter; otherwise, <c>false</c>.
		/// </returns>
		public bool Equals(SourceLocation other)
		{
			return string.Equals(File, other.File) && Start.Equals(other.Start) && End.Equals(other.End);
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

			return obj is SourceLocation && Equals((SourceLocation)obj);
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
				var hashCode = File.GetHashCode();
				hashCode = (hashCode * 397) ^ Start.GetHashCode();
				hashCode = (hashCode * 397) ^ End.GetHashCode();
				return hashCode;
			}
		}

		/// <summary>
		///     Determines whether two specified source locations have the same value.
		/// </summary>
		/// <param name="left">The first line position that should be compared.</param>
		/// <param name="right">The second line position that should be compared.</param>
		/// <returns>
		///     <c>true</c> if the value of <paramref name="left" /> is the same as the value of <paramref name="right" />;
		///     otherwise, <c>false</c>.
		/// </returns>
		public static bool operator ==(SourceLocation left, SourceLocation right)
		{
			return left.Equals(right);
		}

		/// <summary>
		///     Determines whether two specified source locations have different values.
		/// </summary>
		/// <param name="left">The first line position that should be compared.</param>
		/// <param name="right">The second line position that should be compared.</param>
		/// <returns>
		///     <c>true</c> if the value of <paramref name="left" /> is the different from the value of <paramref name="right" />;
		///     otherwise, <c>false</c>.
		/// </returns>
		public static bool operator !=(SourceLocation left, SourceLocation right)
		{
			return !left.Equals(right);
		}
	}
}