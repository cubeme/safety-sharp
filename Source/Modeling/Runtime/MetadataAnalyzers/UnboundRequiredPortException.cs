// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
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

namespace SafetySharp.Runtime.MetadataAnalyzers
{
	using System;
	using Utilities;

	/// <summary>
	///   Raised when a model contains an unbound required port.
	/// </summary>
	public class UnboundRequiredPortException : Exception
	{
		/// <summary>
		///   The exception message.
		/// </summary>
		private const string FormatMessage =
			"Detected an unbound required port: '{0}'; the 'RequiredPort' property contains the metadata of the port for further analysis.";

		/// <summary>
		///   Initializes a new instance.
		/// </summary>
		/// <param name="requiredPort">The metadata of the unbound required port.</param>
		internal UnboundRequiredPortException(RequiredPortMetadata requiredPort)
			: base(String.Format(FormatMessage, requiredPort))
		{
			Requires.NotNull(requiredPort, () => requiredPort);
			RequiredPort = requiredPort;
		}

		/// <summary>
		///   Gets the metadata of the unbound required port.
		/// </summary>
		public RequiredPortMetadata RequiredPort { get; private set; }
	}
}