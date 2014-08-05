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
	using System.Diagnostics;

	/// <summary>
	///     Provides globally accessible functions to log fatal errors, non-fatal errors, warnings, informational messages, and
	///     debug-time only informational messages. The <see cref="Logged" /> event is raised whenever a <see cref="LogEntry" /> has
	///     been generated.
	/// </summary>
	public static class Log
	{
		/// <summary>
		///     Initializes the type.
		/// </summary>
		static Log()
		{
			PrintToDebugOutput();
		}

		/// <summary>
		///     Raised when the <see cref="Die" /> function has completed execution. One of the event handlers is assumed to terminate
		///     the application without returning control to the <see cref="Die" /> function.
		/// </summary>
		public static event Action OnDie;

		/// <summary>
		///     Raised when a <see cref="LogEntry" /> has been generated. If the <see cref="LogEntry" />'s type is
		///     <see cref="LogType.Fatal" />, the program terminates after all event handlers have been executed.
		/// </summary>
		public static event Action<LogEntry> Logged;

		/// <summary>
		///     Logs a fatal application error. After all event handlers of the <see cref="Logged" />
		///     event have been executed, the <see cref="OnDie" /> callback is invoked that is assumed to terminate the application
		///     without returning control to the <see cref="Die" /> function.
		/// </summary>
		/// <param name="message">The non-empty message that should be logged.</param>
		/// <param name="arguments">The arguments that should be used to format <paramref name="message" />.</param>
		[DebuggerHidden, StringFormatMethod("message")]
		public static void Die(string message, params object[] arguments)
		{
			Requires.NotNull(message, () => message);

			RaiseLoggedEvent(LogType.Fatal, String.Format(message, arguments));
			if (OnDie != null)
				OnDie();
		}

		/// <summary>
		///     Logs an application error.
		/// </summary>
		/// <param name="message">The non-empty message that should be logged.</param>
		/// <param name="arguments">The arguments that should be used to format <paramref name="message" />.</param>
		[StringFormatMethod("message")]
		public static void Error(string message, params object[] arguments)
		{
			Requires.NotNull(message, () => message);
			RaiseLoggedEvent(LogType.Error, String.Format(message, arguments));
		}

		/// <summary>
		///     Logs an application warning.
		/// </summary>
		/// <param name="message">The non-empty message that should be logged.</param>
		/// <param name="arguments">The arguments that should be used to format <paramref name="message" />.</param>
		[StringFormatMethod("message")]
		public static void Warn(string message, params object[] arguments)
		{
			Requires.NotNull(message, () => message);
			RaiseLoggedEvent(LogType.Warning, String.Format(message, arguments));
		}

		/// <summary>
		///     Logs an informational message.
		/// </summary>
		/// <param name="message">The non-empty message that should be logged.</param>
		/// <param name="arguments">The arguments that should be used to format <paramref name="message" />.</param>
		[StringFormatMethod("message")]
		public static void Info(string message, params object[] arguments)
		{
			Requires.NotNull(message, () => message);
			RaiseLoggedEvent(LogType.Info, String.Format(message, arguments));
		}

		/// <summary>
		///     In debug builds, logs debugging information.
		/// </summary>
		/// <param name="message">The non-empty message that should be logged.</param>
		/// <param name="arguments">The arguments that should be used to format <paramref name="message" />.</param>
		[Conditional("DEBUG"), StringFormatMethod("message")]
		public static void Debug(string message, params object[] arguments)
		{
			Requires.NotNull(message, () => message);
			RaiseLoggedEvent(LogType.Debug, String.Format(message, arguments));
		}

		/// <summary>
		///     Raises the <see cref="Logged" /> event.
		/// </summary>
		/// <param name="logType">The <see cref="LogType" /> of the <see cref="LogEntry" />.</param>
		/// <param name="message">The message that the <see cref="LogEntry" /> should contain.</param>
		private static void RaiseLoggedEvent(LogType logType, string message)
		{
			if (Logged != null)
				Logged(new LogEntry(logType, message));
		}

		/// <summary>
		///     Writes all generated log messages to the debug output.
		/// </summary>
		private static void PrintToDebugOutput()
		{
			Logged += entry =>
			{
				var type = "";
				switch (entry.LogType)
				{
					case LogType.Debug:
						type = "Debug ";
						break;
					case LogType.Info:
						type = "Info ";
						break;
					case LogType.Warning:
						type = "Warning";
						break;
					case LogType.Error:
						type = "Error ";
						break;
					case LogType.Fatal:
						type = "Fatal ";
						break;
					default:
						Assert.NotReached();
						break;
				}

				System.Diagnostics.Debug.WriteLine("[{0}] {1}", type, entry.Message);
			};
		}
	}
}