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

	/// <summary>
	///     Indicates that the marked method builds strings by format pattern and (optional) arguments. Applying this attribute to
	///     the method with the name of the string format parameter passed to the attribute's constructor allows tools like
	///     Resharper to highlight format parameters and warn about format string and parameter mismatches.
	/// </summary>
	/// <example>
	///     <code>
	/// 			[StringFormatMethod("message")]
	/// 			public void ShowError(string message, params object[] args)
	/// 			{
	/// 			  // ...
	/// 			}
	/// 			public void Foo()
	/// 			{
	/// 			  ShowError("Failed: {0}"); // Warning: Non-existing argument in format string
	/// 			}
	/// 		</code>
	/// </example>
	[AttributeUsage(AttributeTargets.Constructor | AttributeTargets.Method, AllowMultiple = false, Inherited = true)]
	public sealed class StringFormatMethodAttribute : Attribute
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="formatParameterName">The name of the format string parameter.</param>
		public StringFormatMethodAttribute(string formatParameterName)
		{
			Assert.ArgumentNotNullOrWhitespace(formatParameterName, () => formatParameterName);
			FormatParameterName = formatParameterName;
		}

		/// <summary>
		///     Gets the name of the format string parameter.
		/// </summary>
		[UsedImplicitly]
		public string FormatParameterName { get; private set; }
	}
}