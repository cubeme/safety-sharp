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
	using System.Linq;
	using System.Threading;
	using CSharp.Diagnostics;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Microsoft.CodeAnalysis.MSBuild;
	using Utilities;

	internal class SafetySharpProject
	{
		/// <summary>
		///     The MSBuild workspace that contains the project.
		/// </summary>
		private MSBuildWorkspace _workspace;

		/// <summary>
		///     Gets the solution that contains the project.
		/// </summary>
		private Solution Solution
		{
			get { return _workspace.CurrentSolution; }
		}

		/// <summary>
		///     Gets the compilation for the project.
		/// </summary>
		private Compilation Compilation
		{
			get { return Project.GetCompilationAsync().Result; }
		}

		/// <summary>
		///     The C# project representing the Safety Sharp Project.
		/// </summary>
		private Project Project
		{
			get
			{
				var project = Solution.Projects.SingleOrDefault(p => p.FilePath == SafetySharpCompiler.Arguments.ProjectFile);
				Assert.NotNull("Unable to find project '{0}'.", SafetySharpCompiler.Arguments.ProjectFile);

				return project;
			}
		}

		/// <summary>
		///     Compiles the project.
		/// </summary>
		public int Compile()
		{
			_workspace = MSBuildWorkspace.Create();
			_workspace.OpenProjectAsync(SafetySharpCompiler.Arguments.ProjectFile).Wait();

			if (!DiagnoseCode())
				return -1;

			return 0;
		}

		/// <summary>
		///     Runs all diagnostics on the project's code, returning <c>true</c> to indicate that no critical errors have been found
		///     and compilation can continue.
		/// </summary>
		private bool DiagnoseCode()
		{
			var continueCompilation = true;
			var diagnostics = AnalyzerDriver.GetDiagnostics(Compilation, CSharpAnalyzer.GetAnalyzers(), new CancellationToken()).ToArray();

			foreach (var diagnostic in diagnostics)
			{
				switch (diagnostic.Severity)
				{
					case DiagnosticSeverity.Error:
						Log.Error("{0}", diagnostic);
						continueCompilation = false;
						break;
					case DiagnosticSeverity.Warning:
						Log.Warn("{0}", diagnostic);
						break;
					case DiagnosticSeverity.Info:
						Log.Info("{0}", diagnostic);
						break;
					case DiagnosticSeverity.None:
						Log.Debug("{0}", diagnostic);
						break;
					default:
						Assert.NotReached("Unknown C# diagnostic severity.");
						break;
				}
			}

			// Improves readability of generated output
			if (diagnostics.Length != 0)
				Log.Info("");

			return continueCompilation;
		}
	}
}