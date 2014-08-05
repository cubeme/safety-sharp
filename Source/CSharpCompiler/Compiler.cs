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

namespace SafetySharp.CSharpCompiler
{
	using System;
	using System.Collections.Generic;
	using System.Diagnostics;
	using System.IO;
	using System.Linq;
	using System.Threading;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Microsoft.CodeAnalysis.MSBuild;
	using Roslyn;
	using Utilities;

	/// <summary>
	///     Compiles a SafetySharp modeling project authored in C# to SafetySharp modeling assembly.
	/// </summary>
	internal class Compiler
	{
		/// <summary>
		///     Gets the diagnostic analyzers that are used to diagnose the C# code before compilation.
		/// </summary>
		private static IEnumerable<IDiagnosticAnalyzer> GetAnalyzers()
		{
			return from type in typeof(Compiler).Assembly.GetTypes()
				   where type.IsClass && !type.IsAbstract && typeof(IDiagnosticAnalyzer).IsAssignableFrom(type)
				   select (IDiagnosticAnalyzer)Activator.CreateInstance(type);
		}

		/// <summary>
		///     Compiles the SafetySharp modeling project identified by the <paramref name="projectFile" /> for the given
		///     <paramref name="configuration" /> and <paramref name="platform" />.
		/// </summary>
		/// <param name="projectFile">The file of the C# project that should be compiled.</param>
		/// <param name="configuration">The configuration the C# project should be compiled in.</param>
		/// <param name="platform">The platform the C# project should be compiled for.</param>
		public static int Compile(string projectFile, string configuration, string platform)
		{
			Requires.NotNullOrWhitespace(projectFile, () => projectFile);
			Requires.NotNullOrWhitespace(configuration, () => configuration);
			Requires.NotNullOrWhitespace(platform, () => platform);

			if (!File.Exists(projectFile))
				return ReportError("0001", "Project file '{0}' could not be found.", projectFile);

			if (String.IsNullOrWhiteSpace(configuration))
				return ReportError("0002", "Invalid project configuration: Configuration name cannot be the empty string.");

			if (String.IsNullOrWhiteSpace(platform))
				return ReportError("0003", "Invalid compilation platform: Platform name cannot be the empty string.");

			var msBuildProperties = new Dictionary<string, string> { { "Configuration", configuration }, { "Platform", platform } };

			var workspace = MSBuildWorkspace.Create(msBuildProperties);
			var project = workspace.OpenProjectAsync(projectFile).Result;

			var compilation = project.GetCompilationAsync().Result;
			var diagnosticOptions = compilation.Options.SpecificDiagnosticOptions.Add("CS0626", ReportDiagnostic.Suppress);
			var options = compilation.Options.WithSpecificDiagnosticOptions(diagnosticOptions);
			compilation = compilation.WithOptions(options);

			if (!Diagnose(compilation))
				return -1;

			return Emit(compilation, project.OutputFilePath);
		}

		/// <summary>
		///     Reports <paramref name="diagnostic" /> depending on its severity. If <paramref name="errorsOnly" /> is <c>true</c>, only
		///     error diagnostics are reported.
		/// </summary>
		/// <param name="diagnostic">The diagnostic that should be reported.</param>
		/// <param name="errorsOnly">Indicates whether error diagnostics should be reported exclusively.</param>
		private static void Report(Diagnostic diagnostic, bool errorsOnly)
		{
			switch (diagnostic.Severity)
			{
				case DiagnosticSeverity.Error:
					Log.Error("{0}", diagnostic);
					break;
				case DiagnosticSeverity.Warning:
					if (!errorsOnly)
						Log.Warn("{0}", diagnostic);
					break;
				case DiagnosticSeverity.Info:
					if (!errorsOnly)
						Log.Info("{0}", diagnostic);
					break;
				case DiagnosticSeverity.Hidden:
					if (!errorsOnly)
						Log.Debug("{0}", diagnostic);
					break;
				default:
					Assert.NotReached("Unknown diagnostic severity.");
					break;
			}
		}

		/// <summary>
		///     Reports all <paramref name="diagnostics" /> depending on their severities. If <paramref name="errorsOnly" /> is
		///     <c>true</c>, only error diagnostics are reported. The function returns <c>false</c> when at least one error diagnostic
		///     has been reported.
		/// </summary>
		/// <param name="diagnostics">The diagnostics that should be reported.</param>
		/// <param name="errorsOnly">Indicates whether error diagnostics should be reported exclusively.</param>
		private static bool Report(IEnumerable<Diagnostic> diagnostics, bool errorsOnly)
		{
			var containsError = false;
			foreach (var diagnostic in diagnostics)
			{
				Report(diagnostic, errorsOnly);
				containsError |= diagnostic.Severity == DiagnosticSeverity.Error;
			}

			return !containsError;
		}

		/// <summary>
		///     Reports an error diagnostic with the given <paramref name="identifier" /> and <paramref name="message" />.
		/// </summary>
		/// <param name="identifier">The identifier of the diagnostic that should be reported.</param>
		/// <param name="message">The message of the diagnostic that should be reported.</param>
		/// <param name="formatArgs">The format arguments of the message.</param>
		[StringFormatMethod("message")]
		private static int ReportError(string identifier, string message, params object[] formatArgs)
		{
			identifier = CSharpAnalyzer.Prefix + identifier;
			message = String.Format(message, formatArgs);

			var diagnostic = Diagnostic.Create(identifier, CSharpAnalyzer.Category, message, DiagnosticSeverity.Error, true, 0, false);
			Report(diagnostic, true);
			return -1;
		}

		/// <summary>
		///     Writes the C# code contained in the <paramref name="compilation" /> to the directory denoted by
		///     <paramref name="path" />.
		/// </summary>
		/// <param name="compilation">The compilation containing the code that should be output.</param>
		/// <param name="path">The target path the code should be output to.</param>
		[Conditional("DEBUG")]
		private static void OutputCode(Compilation compilation, string path)
		{
			Directory.CreateDirectory(path);
			var index = 0;

			foreach (var syntaxTree in compilation.SyntaxTrees)
			{
				var fileName = Path.GetFileNameWithoutExtension(syntaxTree.FilePath ?? String.Empty);
				var filePath = Path.Combine(path, String.Format("{0}{1}", fileName, index));

				File.WriteAllText(filePath, syntaxTree.GetText().ToString());
				++index;
			}
		}

		/// <summary>
		///     Runs the SafetySharp diagnostic analyzers on the compilation, reporting all generated diagnostics. The function returns
		///     <c>false</c> when at least one error diagnostic has been reported.
		/// </summary>
		/// <param name="compilation">The compilation containing the code that should be diagnosed.</param>
		private static bool Diagnose(Compilation compilation)
		{
			if (!Report(compilation.GetDiagnostics(), true))
				return false;

			var diagnostics = AnalyzerDriver.GetDiagnostics(compilation, GetAnalyzers(), new CancellationToken(), false).ToArray();
			return Report(diagnostics, false);
		}

		/// <summary>
		///     Overwrites the original assembly generated by the C# compiler with the assembly compiled from the rewritten code
		///     contained in the <paramref name="compilation." />
		/// </summary>
		/// <param name="compilation">The compilation containing the code that should be emitted.</param>
		/// <param name="assemblyPath">The target path of the assembly that should be emitted.</param>
		private static int Emit(Compilation compilation, string assemblyPath)
		{
			using (var ilStream = new FileStream(assemblyPath, FileMode.OpenOrCreate))
			using (var pdbStream = new FileStream(Path.ChangeExtension(assemblyPath, ".pdb"), FileMode.OpenOrCreate))
			{
				var emitResult = compilation.Emit(ilStream, pdbStream: pdbStream);

				if (emitResult.Success)
					return 0;

				Report(emitResult.Diagnostics, true);
				return -1;
			}
		}
	}
}