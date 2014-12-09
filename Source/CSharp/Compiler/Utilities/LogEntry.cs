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

namespace SafetySharp.CSharpCompiler.Utilities
{
	using System;

	/// <summary>
	///     Represents a log entry, describing fatal errors, non-fatal errors, or warnings as well as providing debugging
	///     information and other informational messages.
	/// </summary>
	public struct LogEntry
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="logType">The type of the log entry.</param>
		/// <param name="message">The non-empty message of the log entry.</param>
		internal LogEntry(LogType logType, [NotNull] string message)
			: this()
		{
			Requires.InRange(logType, () => logType);
			Requires.NotNull(message, () => message);

			LogType = logType;
			Message = message;
			Time = DateTime.Now;
		}

		/// <summary>
		///     Gets the type of the log entry.
		/// </summary>
		public LogType LogType { get; private set; }

		/// <summary>
		///     Gets the message of the log entry.
		/// </summary>
		[NotNull]
		public string Message { get; private set; }

		/// <summary>
		///     Gets the date and time of the creation of the log entry.
		/// </summary>
		public DateTime Time { get; private set; }
	}
}