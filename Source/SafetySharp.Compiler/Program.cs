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
	using System.Threading;
	using CommandLine;
	using CSharp.Diagnostics;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Microsoft.CodeAnalysis.Emit;
	using Microsoft.CodeAnalysis.MSBuild;
	using Utilities;

	/// <summary>
	///     Represents the entry point to the compiler and sets up all necessary state.
	/// </summary>
	internal static class Program
	{
		/// <summary>
		///     The entry point to the compiler.
		/// </summary>
		/// <param name="args">The compiler arguments passed via the command line.</param>
		private static int Main(string[] args)
		{
			PrintToConsole();

			Log.Info("");

			Log.Info("SafetySharp Compiler");
			Log.Info("Copyright (c) 2014 Institute for Software & Systems Engineering");

			Log.Info("");
			Log.Info("This is free software. You may redistribute copies of it under the terms of");
			Log.Info("the MIT license (see http://opensource.org/licenses/MIT).");

			var arguments = new CompilerArguments();
			using (var parser = new Parser(c => c.HelpWriter = null))
			{
				// Check the arguments for '--help' or '-h' as the command line parser library handles help in a strange
				// way. If so, output the help screen and successfully terminate the application.
				if (args.Any(arg => arg == "--help" || arg == "-h"))
				{
					Log.Info("{0}", arguments.GenerateHelpMessage());
					return -1;
				}

				// If there was an error parsing the command line, show the help screen and terminate the application.
				if (!parser.ParseArguments(args, arguments))
				{
					Log.Info("{0}", arguments.GenerateHelpMessage());
					Log.Die("Invalid command line arguments.");
				}

				// Otherwise, we can start the compilation process.
				Compile(arguments);
			}

			return 0;
		}

		private static void Compile(CompilerArguments arguments)
		{
			var workspace = MSBuildWorkspace.Create();
			var project = workspace.OpenProjectAsync(arguments.ProjectFile).Result;

			var doc = project.Documents.First();
			var root = doc.GetSyntaxRootAsync().Result;
			var returnStatement = root
				.DescendantNodes().OfType<ReturnStatementSyntax>()
				.First();

			var comp = project.GetCompilationAsync().Result;
			var d = AnalyzerDriver.GetDiagnostics(comp, CSharpAnalyzer.GetAnalyzers(), new CancellationToken());

			foreach (var di in d)
				Log.Info("{0}", di);

			var newReturn =
				SyntaxFactory.ReturnStatement(SyntaxFactory.LiteralExpression(SyntaxKind.NumericLiteralExpression,
																			  SyntaxFactory.Literal(SyntaxFactory.TriviaList(
																															 SyntaxFactory.Space), "117", 117, SyntaxFactory.TriviaList())));
			var newRoot = root.ReplaceNode(returnStatement, newReturn);
			//doc = doc.WithSyntaxRoot(newRoot);
			//project = project.RemoveDocument(doc.Id);
			//project = project.AddDocument(doc.Name, newRoot.GetText());

			var solution = workspace.CurrentSolution;
			solution = solution.WithDocumentText(doc.Id, newRoot.GetText());
			project = solution.Projects.Skip(1).First();

			comp = project.GetCompilationAsync().Result;

			Execute(comp, project.OutputFilePath);
		}

		private static void Execute(Compilation comp, string path)
		{
			//var output = new StringBuilder();
			EmitResult emitResult = null;

			using (var ilStream = new FileStream(path, FileMode.OpenOrCreate))
			{
				// Emit IL, PDB and xml documentation comments for the compilation to disk.
				emitResult = comp.Emit(ilStream);
			}

			if (!emitResult.Success)
			{
				//output.AppendLine("Errors:");
				foreach (var diag in emitResult.Diagnostics)
				{
					Log.Error("{0}", diag);
				}
			}

			//return output.ToString();
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
						WriteToConsole(ConsoleColor.Magenta, entry);
						break;
					case LogType.Info:
						WriteToConsole(ConsoleColor.White, entry);
						break;
					case LogType.Warning:
						WriteToConsole(ConsoleColor.Yellow, entry);
						break;
					case LogType.Error:
						WriteToConsole(ConsoleColor.Red, entry);
						break;
					case LogType.Fatal:
						WriteToConsole(ConsoleColor.Red, entry);
						break;
					default:
						Assert.NotReached();
						break;
				}
			};
		}

		/// <summary>
		///     Writes the <paramref name="entry" /> to the console using the given font <paramref name="color" />.
		/// </summary>
		/// <param name="color">The color that should be used to write <paramref name="entry" /> to the console.</param>
		/// <param name="entry">The entry that should be written to the console.</param>
		private static void WriteToConsole(ConsoleColor color, LogEntry entry)
		{
			var currentColor = Console.ForegroundColor;

			Console.ForegroundColor = color;
			Console.WriteLine(entry.Message);
			Console.ForegroundColor = currentColor;
		}
	}
}