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

namespace SafetySharp.Compiler
{
	using System;
	using System.Linq;
	using CommandLine;
	using CommandLine.Text;
	using JetBrains.Annotations;
	using Runtime.Utilities;

	/// <summary>
	///     Parses the command line arguments and starts the compilation process.
	/// </summary>
	internal class Program
	{
		/// <summary>
		///     Gets or sets the name of the configuration that should be used to compile the project.
		/// </summary>
		[Option("configuration", Required = true, HelpText = "The name of the configuration that should be used to compile the project.")]
		[UsedImplicitly]
		public string Configuration { get; set; }

		/// <summary>
		///     Gets or sets the name of the platform that should be used to compile the project.
		/// </summary>
		[Option("platform", Required = true, HelpText = "The name of the platform that should be used to compile the project.")]
		[UsedImplicitly]
		public string Platform { get; set; }

		/// <summary>
		///     Gets or sets the path to the C# project file that should be compiled.
		/// </summary>
		[Option("project", Required = true, HelpText = "The path to the C# project file that should be compiled.")]
		[UsedImplicitly]
		public string ProjectFile { get; set; }

		/// <summary>
		///     Gets or sets a value indicating whether all compiler output should be suppressed.
		/// </summary>
		[Option("silent", Required = false, HelpText = "Suppresses all compiler output except for errors and warnings.")]
		[UsedImplicitly]
		public bool Silent { get; set; }

		/// <summary>
		///     Generates a help message about the correct usage of the compiler's command line arguments.
		/// </summary>
		[HelpOption('h', "help")]
		[UsedImplicitly]
		public string GenerateHelpMessage()
		{
			var help = new HelpText
			{
				AdditionalNewLineAfterOption = true,
				AddDashesToOption = true
			};

			help.AddOptions(this);
			return help.ToString();
		}

		/// <summary>
		///     Runs the compilation process.
		/// </summary>
		/// <param name="args">The compiler arguments passed via the command line.</param>
		private int Compile(string[] args)
		{
			PrintToConsole();

			using (var parser = new Parser(c => c.HelpWriter = null))
			{
				// Check the arguments for '--help' or '-h' as the command line parser library handles help in a strange
				// way. If so, output the help screen and successfully terminate the application.
				if (args.Any(arg => arg == "--help" || arg == "-h"))
				{
					Log.Info("{0}", GenerateHelpMessage());
					return 0;
				}

				// If there was an error parsing the command line, show the help screen and terminate the application.
				if (!parser.ParseArguments(args, this))
				{
					Silent = false;
					Log.Info("{0}", GenerateHelpMessage());
					Log.Die("Invalid command line arguments.");
				}
			}

			Log.Info("");

			Log.Info("S# Compiler");
			Log.Info("Copyright (c) 2014 Institute for Software & Systems Engineering");

			Log.Info("");
			Log.Info("This is free software. You may redistribute copies of it under the terms of");
			Log.Info("the MIT license (see http://opensource.org/licenses/MIT).");

			Log.Info("");

			// Start the compilation process.
			try
			{
				var compiler = new Compiler(testing: false);
				if (!compiler.Compile(ProjectFile, Configuration, Platform))
					return -1;

				Log.Info("Compilation completed successfully.");
				return 0;
			}
			catch (Exception e)
			{
				Log.Error("A fatal compilation error occurred: {0}", e.Message);
#if DEBUG
				Log.Error("StackTrace:\n{0}", e.StackTrace);
#endif
				return -1;
			}
		}

		/// <summary>
		///     Wires up the <see cref="Log.Logged" /> event to write all logged messages to the console.
		/// </summary>
		private void PrintToConsole()
		{
			Log.Logged += entry =>
			{
				switch (entry.LogType)
				{
					case LogType.Info:
						if (!Silent)
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
		private static void WriteToConsole(ConsoleColor color, [NotNull] string message)
		{
			var currentColor = Console.ForegroundColor;

			Console.ForegroundColor = color;
			Console.WriteLine(message);
			Console.ForegroundColor = currentColor;
		}

		/// <summary>
		///     The entry point to the compiler.
		/// </summary>
		/// <param name="args">The compiler arguments passed via the command line.</param>
		private static int Main(string[] args)
		{
			Log.OnDie += () => Environment.Exit(-1);

			var program = new Program();
			return program.Compile(args);
		}
	}
}