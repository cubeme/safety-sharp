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

namespace SafetySharp.Compiler
{
	using System;
	using System.IO;
	using System.Linq;
	using CommandLine;
	using Utilities;

	/// <summary>
	///     Represents the entry point to the compiler and sets up all necessary state.
	/// </summary>
	internal static class SafetySharpCompiler
	{
		/// <summary>
		///     Gets the command line arguments that have been used to invoke the compiler.
		/// </summary>
		internal static CompilationArguments Arguments { get; private set; }

		/// <summary>
		///     The entry point to the compiler.
		/// </summary>
		/// <param name="args">The compiler arguments passed via the command line.</param>
		private static int Main(string[] args)
		{
			PrintToConsole();

			Arguments = new CompilationArguments();
			using (var parser = new Parser(c => c.HelpWriter = null))
			{
				// Check the arguments for '--help' or '-h' as the command line parser library handles help in a strange
				// way. If so, output the help screen and successfully terminate the application.
				if (args.Any(arg => arg == "--help" || arg == "-h"))
				{
					Log.Info("{0}", Arguments.GenerateHelpMessage());
					return 0;
				}

				// If there was an error parsing the command line, show the help screen and terminate the application.
				if (!parser.ParseArguments(args, Arguments))
				{
					Arguments.Silent = false;
					Log.Info("{0}", Arguments.GenerateHelpMessage());
					Log.Die("Invalid command line arguments.");
				}

				// Argument validation
				if (!File.Exists(Arguments.ProjectFile))
					Log.Die("Project file '{0}' could not be found.", Arguments.ProjectFile);
			}

			Log.Info("");

			Log.Info("SafetySharp Compiler");
			Log.Info("Copyright (c) 2014 Institute for Software & Systems Engineering");

			Log.Info("");
			Log.Info("This is free software. You may redistribute copies of it under the terms of");
			Log.Info("the MIT license (see http://opensource.org/licenses/MIT).");

			Log.Info("");

			// Start the compilation process.
			var project = new SafetySharpProject();
			var resultCode = project.Compile();

			if (resultCode == 0)
				Log.Info("Compilation completed successfully.");

			return resultCode;
		}

		/// <summary>
		///     Wires up the <see cref="Log.Logged" /> event to write all logged messages to the console.
		/// </summary>
		private static void PrintToConsole()
		{
			Log.Logged += entry =>
			{
				switch (entry.LogType)
				{
					case LogType.Debug:
						if (!Arguments.Silent)
							WriteToConsole(ConsoleColor.Magenta, entry.Message);
						break;
					case LogType.Info:
						if (!Arguments.Silent)
							WriteToConsole(ConsoleColor.White, entry.Message);
						break;
					case LogType.Warning:
						WriteToConsole(ConsoleColor.Yellow, entry.Message);
						break;
					case LogType.Error:
						WriteToConsole(ConsoleColor.Red, entry.Message);
						break;
					case LogType.Fatal:
						WriteToConsole(ConsoleColor.Red, entry.Message);
						break;
					default:
						Assert.NotReached();
						break;
				}
			};
		}

		/// <summary>
		///     Writes the <paramref name="message" /> to the console using the given <paramref name="color" />.
		/// </summary>
		/// <param name="color">The color that should be used to write <paramref name="message" /> to the console.</param>
		/// <param name="message">The message that should be written to the console.</param>
		private static void WriteToConsole(ConsoleColor color, string message)
		{
			var currentColor = Console.ForegroundColor;

			Console.ForegroundColor = color;
			Console.WriteLine(message);
			Console.ForegroundColor = currentColor;
		}
	}
}