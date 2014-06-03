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

namespace SafetySharp.CSharp
{
	using System;
	using System.Collections.Generic;
	using System.Diagnostics;
	using System.IO;
	using System.Linq;
	using System.Text;
	using System.Threading;
	using Diagnostics;
	using Extensions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Microsoft.CodeAnalysis.Emit;
	using Microsoft.CodeAnalysis.MSBuild;
	using Modeling;
	using Normalization;
	using Utilities;

	/// <summary>
	///     The Safety Sharp compiler that compiles C# code into a modeling assembly.
	/// </summary>
	public class Compiler
	{
		/// <summary>
		///     The prefix that is used for all diagnostic identifiers.
		/// </summary>
		internal const string DiagnosticsPrefix = "SS";

		/// <summary>
		///     The category that is used for all diagnostics.
		/// </summary>
		internal const string DiagnosticsCategory = "Safety Sharp";

		/// <summary>
		///     The version string of the compiler.
		/// </summary>
		internal const string Version = "0.0.1-beta";

		/// <summary>
		///     The file name of the SafetySharp.Modeling assembly.
		/// </summary>
		private const string ModelingAssemblyFileName = "SafetySharp.Modeling.dll";

		/// <summary>
		///     The path to the emitted assembly file of the project.
		/// </summary>
		private string _assemblyPath;

		/// <summary>
		///     The compilation for the project.
		/// </summary>
		private Compilation _compilation;

		/// <summary>
		///     The reference to the SafetySharp.Modeling assembly imported by the project.
		/// </summary>
		private PortableExecutableReference _modelingAssembly;

		/// <summary>
		///     The path to the C# project file that is being compiled.
		/// </summary>
		private string _projectFile;

		/// <summary>
		///     Compiles the C# modeling project.
		/// </summary>
		/// <param name="projectFile">The path to the C# project file that should be compiled.</param>
		/// <param name="configuration">The name of the project configuration that should be used for compilation.</param>
		/// <param name="platform">The name of the project platform that should be the target of the compilation.</param>
		public int Compile(string projectFile, string configuration, string platform)
		{
			Argument.NotNull(projectFile, () => projectFile);
			Argument.NotNull(configuration, () => configuration);
			Argument.NotNull(platform, () => platform);

			if (!File.Exists(projectFile))
				return LogError("0001", "Project file '{0}' could not be found.", projectFile);

			if (String.IsNullOrWhiteSpace(configuration))
				return LogError("0002", "Invalid project configuration: Configuration name cannot be the empty string.");

			if (String.IsNullOrWhiteSpace(platform))
				return LogError("0003", "Invalid compilation platform: Platform name cannot be the empty string.");

			var msBuildProperties = new[]
			{
				new KeyValuePair<string, string>("Configuration", configuration),
				new KeyValuePair<string, string>("Platform", platform)
			};

			var workspace = MSBuildWorkspace.Create(msBuildProperties);
			var project = workspace.OpenProjectAsync(projectFile).Result;

			_projectFile = projectFile;
			_compilation = project.GetCompilationAsync().Result;
			_assemblyPath = project.OutputFilePath;

			if (!Diagnose())
				return -1;

			Normalize();
			return Emit();
		}

		/// <summary>
		///     Runs all diagnostics on the project's code, returning <c>true</c> to indicate that no critical errors have been found
		///     and compilation can continue.
		/// </summary>
		private bool Diagnose()
		{
			_modelingAssembly = _compilation
				.References
				.OfType<PortableExecutableReference>()
				.SingleOrDefault(reference => Path.GetFileName(reference.FullPath) == ModelingAssemblyFileName);

			if (_modelingAssembly == null)
				Log.Die("{0}: error: Assembly '{1}' is not referenced.", _projectFile, ModelingAssemblyFileName);

			var diagnostics = AnalyzerDriver.GetDiagnostics(_compilation, CSharpAnalyzer.GetAnalyzers(), new CancellationToken()).ToArray();
			foreach (var diagnostic in diagnostics)
				LogDiagnostic(diagnostic);

			return diagnostics.All(diagnostic => diagnostic.Severity != DiagnosticSeverity.Error);
		}

		/// <summary>
		///     Applies of series of compile-time Safety Sharp modeling code normalizations.
		/// </summary>
		private void Normalize()
		{
			// We swap out the referenced SafetySharp.Modeling assembly with the Safety Sharp core assembly behind the
			// modeler's back. This enables a couple of C# normalizations required for debugging, simulation and model
			// transformations while only surfacing a minimal and convenient API for model creation.
			var safetySharpAssembly = new MetadataFileReference(typeof(Component).Assembly.Location);
			_compilation = _compilation.ReplaceReference(_modelingAssembly, safetySharpAssembly);

			// Now that we've replaced SafetySharp.Modeling, we can safely perform the compile-time normalizations of the C# modeling code.
			// We'll first apply some common normalizations before the compilation is split into the metadata code and the simulation code.
			// The metadata code is added as metadata to the generated assembly and is used at runtime for model transformations. The
			// simulation code is compiled to regular MSIL and executed during simulation.
			ApplyCommonNormalizations();
			ApplyMetadataNormalizations();
			ApplySimulationNormalizations();

			OutputCode(_compilation, "obj/NormalizedCode");
		}

		/// <summary>
		///     Applies normalizations for both the metadata code and the simulation code.
		/// </summary>
		private void ApplyCommonNormalizations()
		{
			// TODO
		}

		/// <summary>
		///     Applies normalizations to the metadata code and adds the normalized metadata code to the assembly.
		/// </summary>
		private void ApplyMetadataNormalizations()
		{
			var metadataCompilation = _compilation;

			metadataCompilation = ApplyNormalizer<TypesNormalizer>(metadataCompilation);
			metadataCompilation = ApplyNormalizer<ChooseNormalizer>(metadataCompilation);

			OutputCode(metadataCompilation, "obj/MetadataCode");
			AddMetadata(metadataCompilation);
		}

		/// <summary>
		///     Applies normalizations to the simulation code.
		/// </summary>
		private void ApplySimulationNormalizations()
		{
			_compilation = ApplyNormalizer<StateFormulaNormalizer>(_compilation);
		}

		/// <summary>
		///     Adds the metadata from the <paramref name="metadataCompilation" /> to the generated assembly.
		/// </summary>
		/// <param name="metadataCompilation">The metadata code that should be added.</param>
		private void AddMetadata(Compilation metadataCompilation)
		{
			var csharpCode = new StringBuilder();
			var compilationUnits = metadataCompilation
				.SyntaxTrees
				.SelectMany(syntaxTree => syntaxTree.DescendantNodesAndSelf<CompilationUnitSyntax>());

			foreach (var compilationUnit in compilationUnits)
			{
				var attributeName = typeof(ModelingCompilationUnitAttribute).FullName;
				var content = compilationUnit.ToString().Trim().Replace("\"", "\"\"");
				var fileName = compilationUnit.SyntaxTree.FilePath.Replace("\\", "\\\\");

				csharpCode.AppendLine(String.Format("[assembly: {0}(@\"{1}\", \"{2}\")]", attributeName, content, fileName));
			}

			csharpCode.AppendLine(String.Format("[assembly: {0}(\"{1}\")]", typeof(ModelingAssemblyAttribute).FullName, Version));
			_compilation = _compilation.AddSyntaxTrees(SyntaxFactory.ParseSyntaxTree(csharpCode.ToString()));
		}

		/// <summary>
		///     Applies the normalizer of type <typeparamref name="TNormalizer" /> to the C# <paramref name="compilation" />.
		/// </summary>
		/// <typeparam name="TNormalizer">The type of the normalizer that should be applied.</typeparam>
		/// <param name="compilation">The compilation that should be normalized.</param>
		private static Compilation ApplyNormalizer<TNormalizer>(Compilation compilation)
			where TNormalizer : CSharpNormalizer, new()
		{
			var normalizer = new TNormalizer();
			return normalizer.Normalize(compilation);
		}

		/// <summary>
		///     Overwrites the original assembly generated by the C# compiler with the assembly compiled from the rewritten code.
		/// </summary>
		private int Emit()
		{
			EmitResult emitResult;

			using (var ilStream = new FileStream(_assemblyPath, FileMode.OpenOrCreate))
			using (var pdbStream = new FileStream(Path.ChangeExtension(_assemblyPath, ".pdb"), FileMode.OpenOrCreate))
				emitResult = _compilation.Emit(ilStream, pdbStream: pdbStream);

			if (emitResult.Success)
				return 0;

			foreach (var diagnostic in emitResult.Diagnostics)
				LogDiagnostic(diagnostic);

			return -1;
		}

		/// <summary>
		///     Logs <paramref name="diagnostic" /> depending on its severity.
		/// </summary>
		/// <param name="diagnostic">The diagnostic that should be logged.</param>
		private static void LogDiagnostic(Diagnostic diagnostic)
		{
			switch (diagnostic.Severity)
			{
				case DiagnosticSeverity.Error:
					Log.Error("{0}", diagnostic);
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

		/// <summary>
		///     Instantiates a <see cref="Diagnostic" /> for the error and logs it.
		/// </summary>
		/// <param name="identifier">The identifier of the diagnostic.</param>
		/// <param name="message">The format message of the diagnostic.</param>
		/// <param name="formatArgs">The format arguments that should be used to format <paramref name="message" />.</param>
		[StringFormatMethod("message")]
		private static int LogError(string identifier, string message, params object[] formatArgs)
		{
			LogDiagnostic(Diagnostic.Create(
				id: DiagnosticsPrefix + identifier,
				category: DiagnosticsCategory,
				message: String.Format(message, formatArgs),
				severity: DiagnosticSeverity.Error,
				warningLevel: 0,
				isWarningAsError: false));

			return -1;
		}

		/// <summary>
		///     Writes the C# code contained in the <paramref name="compilation" /> to the directory denoted by
		///     <paramref name="path" />.
		/// </summary>
		/// <param name="compilation">The compilation containing the C# code that should be output.</param>
		/// <param name="path">The path to the directory that should contain the output.</param>
		[Conditional("DEBUG")]
		private static void OutputCode(Compilation compilation, string path)
		{
			Directory.CreateDirectory(path);

			var i = 0;
			foreach (var syntaxTree in compilation.SyntaxTrees)
			{
				var fileName = Path.GetFileNameWithoutExtension(syntaxTree.FilePath ?? String.Empty);
				var filePath = Path.Combine(path, String.Format("{0}{1}.cs", fileName, i++));

				File.WriteAllText(filePath, syntaxTree.GetText().ToString());
			}
		}
	}
}