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
	using CommandLine;
	using CommandLine.Text;

	/// <summary>
	///     Provides access to the command line arguments that have been provided to the compiler.
	/// </summary>
	internal class CommandLineArguments
	{
		/// <summary>
		///     Gets or sets the name of the configuration that should be used to compile the project.
		/// </summary>
		[Option("configuration", Required = true, HelpText = "The name of the configuration that should be used to compile the project.")]
		public string Configuration { get; set; }

		/// <summary>
		///     Gets or sets the name of the platform that should be used to compile the project.
		/// </summary>
		[Option("platform", Required = true, HelpText = "The name of the platform that should be used to compile the project.")]
		public string Platform { get; set; }

		/// <summary>
		///     Gets or sets the path to the C# project file that should be compiled.
		/// </summary>
		[Option("project", Required = true, HelpText = "The path to the C# project file that should be compiled.")]
		public string ProjectFile { get; set; }

		/// <summary>
		///     Gets or sets a value indicating whether all compiler output should be suppressed.
		/// </summary>
		[Option("silent", Required = false, HelpText = "Suppresses all compiler output except for errors and warnings.")]
		public bool Silent { get; set; }

		/// <summary>
		///     Generates a help message about the correct usage of the compiler's command line arguments.
		/// </summary>
		[HelpOption('h', "help")]
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
	}
}