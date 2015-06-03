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
	using System.Collections.Generic;
	using System.Collections.Immutable;
	using System.Diagnostics;
	using System.IO;
	using System.Linq;
	using CSharp.Roslyn;
	using CSharp.Utilities;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Microsoft.CodeAnalysis.MSBuild;
	using Normalization;

	/// <summary>
	///     Compiles a S# modeling project authored in C# to a S# modeling assembly.
	/// </summary>
	internal class Compiler
	{
		/// <summary>
		///     The diagnostic analyzers that are used to diagnose the C# code before compilation.
		/// </summary>
		private static ImmutableArray<DiagnosticAnalyzer> _analyzers;

		/// <summary>
		///     Indicates whether the compiler is used to compile test code.
		/// </summary>
		private readonly bool _testing;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="testing">Indicates whether the compile is used to compile test code.</param>
		public Compiler(bool testing)
		{
			_testing = testing;
		}

		/// <summary>
		///     Gets the diagnostic analyzers that are used to diagnose the C# code before compilation.
		/// </summary>
		private static ImmutableArray<DiagnosticAnalyzer> Analyzers
		{
			get
			{
				if (_analyzers.IsDefault)
				{
					_analyzers = typeof(Analyzer)
						.Assembly.GetTypes()
						.Where(type => type.IsClass && !type.IsAbstract && typeof(DiagnosticAnalyzer).IsAssignableFrom(type))
						.Select(type => (DiagnosticAnalyzer)Activator.CreateInstance(type))
						.ToImmutableArray();
				}

				return _analyzers;
			}
		}

		/// <summary>
		///     Compiles the S# modeling project identified by the <paramref name="projectFile" /> for the given
		///     <paramref name="configuration" /> and <paramref name="platform" />.
		/// </summary>
		/// <param name="projectFile">The C# project file that should be compiled.</param>
		/// <param name="configuration">The configuration the C# project should be compiled in.</param>
		/// <param name="platform">The platform the C# project should be compiled for.</param>
		public bool Compile([NotNull] string projectFile, [NotNull] string configuration, [NotNull] string platform)
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

			return Compile(project, project.OutputFilePath, runSSharpDiagnostics: true);
		}

		/// <summary>
		///     Compiles the S# <paramref name="project" />.
		/// </summary>
		/// <param name="project">The project that should be compiled.</param>
		/// <param name="outputPath">The output path of the compiled assembly.</param>
		/// <param name="runSSharpDiagnostics">Indicates whether S#-specific diagnostics should be run.</param>
		public bool Compile([NotNull] Project project, [NotNull] string outputPath, bool runSSharpDiagnostics)
		{
			Requires.NotNull(project, () => project);
			Requires.NotNullOrWhitespace(outputPath, () => outputPath);

			var compilation = project.GetCompilationAsync().Result;

			if (!Diagnose(compilation, runSSharpDiagnostics))
				return false;

			var optimizedCompilation = compilation.WithOptions(compilation.Options.WithOptimizationLevel(OptimizationLevel.Release));
			var originalAssembly = EmitToStream(optimizedCompilation);
			if (originalAssembly == null)
				return false;

			var diagnosticOptions = compilation.Options.SpecificDiagnosticOptions.Add("CS0626", ReportDiagnostic.Suppress);
			var options = compilation.Options.WithSpecificDiagnosticOptions(diagnosticOptions);

			compilation = compilation.WithOptions(options);
			compilation = NormalizeSimulationCode(compilation);

			originalAssembly.Position = 0;
			return Emit(compilation, outputPath, originalAssembly);
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
				case DiagnosticSeverity.Hidden:
					if (!errorsOnly)
						Log.Info("{0}", diagnostic);
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
		private static bool Report([NotNull] IEnumerable<Diagnostic> diagnostics, bool errorsOnly)
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
		private static bool ReportError([NotNull] string identifier, [NotNull] string message, params object[] formatArgs)
		{
			identifier = DiagnosticInfo.Prefix + identifier;
			message = String.Format(message, formatArgs);

			var diagnostic = Diagnostic.Create(identifier, DiagnosticInfo.Category, message, DiagnosticSeverity.Error,
				DiagnosticSeverity.Error, true, 0);
			Report(diagnostic, true);
			return false;
		}

		/// <summary>
		///     Writes the C# code contained in the <paramref name="compilation" /> to the directory denoted by
		///     <paramref name="path" />.
		/// </summary>
		/// <param name="compilation">The compilation containing the code that should be output.</param>
		/// <param name="path">The target path the code should be output to.</param>
		[Conditional("DEBUG")]
		private void OutputCode([NotNull] Compilation compilation, [NotNull] string path)
		{
			if (_testing)
				return;

			path = Path.Combine("obj", path);
			Directory.CreateDirectory(path);

			var index = 0;
			foreach (var syntaxTree in compilation.SyntaxTrees)
			{
				var fileName = Path.GetFileNameWithoutExtension(syntaxTree.FilePath ?? String.Empty);
				var filePath = Path.Combine(path, String.Format("{0}{1}.cs", fileName, index));

				File.WriteAllText(filePath, syntaxTree.GetText().ToString());
				++index;
			}
		}

		/// <summary>
		///     Runs the S# diagnostic analyzers on the compilation, reporting all generated diagnostics. The function returns
		///     <c>false</c> when at least one error diagnostic has been reported.
		/// </summary>
		/// <param name="compilation">The compilation containing the code that should be diagnosed.</param>
		/// <param name="runSSharpDiagnostics">Indicates whether S#-specific diagnostics should be run.</param>
		private bool Diagnose([NotNull] Compilation compilation, bool runSSharpDiagnostics)
		{
			if (!Report(compilation.GetDiagnostics(), true))
				return false;

			if (!runSSharpDiagnostics)
				return true;

			return Report(compilation.WithAnalyzers(Analyzers).GetAnalyzerDiagnosticsAsync().Result, false);
		}

		/// <summary>
		///     Applies a normalizer of type <typeparamref name="T" /> to the <paramref name="compilation." />
		/// </summary>
		/// <typeparam name="T">The type of the normalizer that should be applied to <paramref name="compilation" />.</typeparam>
		/// <param name="compilation">The compilation that should be normalized.</param>
		[NotNull]
		private static Compilation ApplyNormalizer<T>([NotNull] Compilation compilation)
			where T : Normalizer, new()
		{
			return new T().Normalize(compilation);
		}

		/// <summary>
		///     Applies the required normalizations to the simulation code.
		/// </summary>
		/// <param name="compilation">The compilation that should be normalized.</param>
		[NotNull]
		private Compilation NormalizeSimulationCode([NotNull] Compilation compilation)
		{
			compilation = ApplyNormalizer<DebugInfoNormalizer>(compilation);
			compilation = ApplyNormalizer<PartialNormalizer>(compilation);
			compilation = ApplyNormalizer<ExpressionLifter>(compilation);
			compilation = ApplyNormalizer<PortNormalizer>(compilation);
			compilation = ApplyNormalizer<BindingNormalizer>(compilation);

			OutputCode(compilation, "Simulation");
			return compilation;
		}

		/// <summary>
		///     Overwrites the original assembly generated by the C# compiler with the assembly compiled from the rewritten code
		///     contained in the <paramref name="compilation" />.
		/// </summary>
		/// <param name="compilation">The compilation containing the code that should be emitted.</param>
		/// <param name="assemblyPath">The target path of the assembly that should be emitted.</param>
		/// <param name="embeddedAssembly">The stream of the assembly that should be embedded.</param>
		private static bool Emit([NotNull] Compilation compilation, [NotNull] string assemblyPath, [NotNull] Stream embeddedAssembly)
		{
			var resources = new[]
			{
				new ResourceDescription(Reflection.EmbeddedAssembly, () => embeddedAssembly, true)
			};

			var emitResult = compilation.Emit(assemblyPath, Path.ChangeExtension(assemblyPath, ".pdb"), manifestResources: resources);
			if (emitResult.Success)
				return true;

			Report(emitResult.Diagnostics, true);
			return false;
		}

		/// <summary>
		///     Returns the stream of the emitted code for the <paramref name="compilation" />.
		/// </summary>
		/// <param name="compilation">The compilation containing the code that should be emitted.</param>
		private static MemoryStream EmitToStream([NotNull] Compilation compilation)
		{
			var stream = new MemoryStream();
			var emitResult = compilation.Emit(stream);
			if (emitResult.Success)
				return stream;

			Report(emitResult.Diagnostics, true);
			return null;
		}
	}
}