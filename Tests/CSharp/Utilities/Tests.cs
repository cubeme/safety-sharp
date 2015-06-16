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

namespace Tests.Utilities
{
	using System;
	using System.Collections.Generic;
	using System.Collections.Immutable;
	using System.IO;
	using System.Linq;
	using System.Reflection;
	using System.Runtime.CompilerServices;
	using System.Text;
	using Diagnostics;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Diagnostics;
	using SafetySharp.Compiler;
	using SafetySharp.Compiler.Analyzers;
	using SafetySharp.Compiler.Normalization;
	using SafetySharp.Compiler.Roslyn.Symbols;
	using SafetySharp.Compiler.Roslyn.Syntax;
	using SafetySharp.CompilerServices;
	using SafetySharp.Modeling;
	using SafetySharp.Utilities;
	using Shouldly;
	using Xunit.Abstractions;

	/// <summary>
	///     A base class for all S# tests.
	/// </summary>
	public class Tests
	{
		/// <summary>
		///     Writes to the test output stream.
		/// </summary>
		private readonly ITestOutputHelper _output;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="output">The stream that should be used to write the test output.</param>
		protected Tests(ITestOutputHelper output = null)
		{
			_output = output;
		}

		/// <summary>
		///     Writes the formatted <paramref name="message" /> to the test output stream.
		/// </summary>
		/// <param name="message">The formatted message that should be written.</param>
		/// <param name="args">The format arguments of the message.</param>
		[StringFormatMethod("message")]
		protected void Log(string message, params object[] args)
		{
			Assert.NotNull(_output, "A test output helper must be provided via the constructor.");
			_output.WriteLine(message, args);
		}

		/// <summary>
		///     Gets the name of the file that calls this method.
		/// </summary>
		/// <param name="filePath">The name of the file; passed automatically by the C# compiler.</param>
		protected static string GetFileName([CallerFilePath] string filePath = null)
		{
			return filePath;
		}

		/// <summary>
		///     Executes the <see cref="TestComponent.Check" /> methods of all <see cref="TestComponent" /> instances declared in
		///     <paramref name="syntaxTree" />.
		/// </summary>
		/// <param name="syntaxTree">The syntax tree that should be compiled and tested.</param>
		protected void ExecuteComponentTests(SyntaxTree syntaxTree)
		{
			var compilation = CreateCompilation(syntaxTree);
			var semanticModel = compilation.GetSemanticModel(syntaxTree);

			var componentTypes = syntaxTree
				.Descendants<ClassDeclarationSyntax>()
				.Select(declaration => declaration.GetTypeSymbol(semanticModel))
				.Where(symbol => !symbol.IsGenericType && !symbol.IsAbstract && symbol.ContainingType == null)
				.Where(symbol => symbol.IsDerivedFrom(semanticModel.GetTypeSymbol<TestComponent>()))
				.Select(symbol => symbol.ToDisplayString())
				.ToArray();

			if (componentTypes.Length == 0)
				throw new TestException("Unable to find any testable class declarations.");

			var assembly = CompileSafetySharp(compilation);

			foreach (var componentType in componentTypes)
			{
				var type = assembly.GetType(componentType);
				var component = (TestComponent)Activator.CreateInstance(type);
				MetadataBuilders.GetBuilder(component).RegisterMetadata();

				component.RunTests();
			}
		}

		/// <summary>
		///     Creates a compilation for the <paramref name="compilationUnits" />.
		/// </summary>
		/// <param name="compilationUnits">The compilation units the compilation should contain.</param>
		protected static Compilation CreateCompilation(params string[] compilationUnits)
		{
			return CreateCompilation(compilationUnits.Select(unit => SyntaxFactory.ParseSyntaxTree(unit)).ToArray());
		}

		/// <summary>
		///     Creates a compilation for the <paramref name="syntaxTrees" />.
		/// </summary>
		/// <param name="syntaxTrees">The syntax trees the compilation should contain.</param>
		protected static Compilation CreateCompilation(params SyntaxTree[] syntaxTrees)
		{
			var compilation = CSharpCompilation
				.Create("DynamicTestAssembly")
				.WithOptions(new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary))
				.AddSyntaxTrees(syntaxTrees)
				.AddReferences(MetadataReference.CreateFromAssembly(typeof(object).Assembly))
				.AddReferences(MetadataReference.CreateFromAssembly(typeof(DynamicAttribute).Assembly))
				.AddReferences(MetadataReference.CreateFromAssembly(typeof(Component).Assembly))
				.AddReferences(MetadataReference.CreateFromAssembly(typeof(DiagnosticAttribute).Assembly))
				.AddReferences(MetadataReference.CreateFromAssembly(typeof(DiagnosticIdentifier).Assembly))
				.AddReferences(MetadataReference.CreateFromAssembly(typeof(Should).Assembly))
				.AddReferences(MetadataReference.CreateFromAssembly(typeof(ImmutableArray).Assembly))
				.AddReferences(MetadataReference.CreateFromAssembly(typeof(DiagnosticIdentifier).Assembly))
				.AddReferences(MetadataReference.CreateFromAssembly(typeof(BindingNormalizer).Assembly));

			var errors = compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error).ToArray();
			if (errors.Length != 0)
				throw new CSharpException(errors, "Failed to create compilation.");

			return compilation;
		}

		/// <summary>
		///     Runs the S# analyzers on the given compilation, ensuring that the compilation contains no errors.
		/// </summary>
		/// <param name="compilation">The compilation that should be checked.</param>
		protected static void CheckForSSharpDiagnostics(Compilation compilation)
		{
			var errors = compilation
				.WithAnalyzers(Compiler.Analyzers)
				.GetAllDiagnosticsAsync().Result
				.Where(d => d.Severity == DiagnosticSeverity.Error && !d.Id.StartsWith("CS"))
				.ToArray();

			if (errors.Length != 0)
				throw new CSharpException(errors, "Failed to create compilation.");
		}

		/// <summary>
		///     Compiles the <paramref name="compilation" /> with the S# compiler and returns the resulting assembly that has been
		///     loaded into the app domain.
		/// </summary>
		/// <param name="compilation">The compilation that should be compiled.</param>
		protected Assembly CompileSafetySharp(Compilation compilation)
		{
			using (var workspace = new AdhocWorkspace())
			{
				var project = workspace
					.AddProject(compilation.AssemblyName, LanguageNames.CSharp)
					.AddMetadataReferences(compilation.References)
					.WithCompilationOptions(compilation.Options);

				foreach (var syntaxTree in compilation.SyntaxTrees)
					project = project.AddDocument(syntaxTree.FilePath, syntaxTree.GetRoot().GetText(Encoding.UTF8)).Project;

				var errorReporter = new CSharpErrorReporter(_output);
				var compiler = new Compiler(errorReporter);

				try
				{
					var assembly = compiler.Compile(project);
					Log("{0}", SyntaxTreesToString(compiler.Compilation));

					return assembly;
				}
				catch (CompilationException e)
				{
					throw new TestException("{0}\n\n{1}", e.Message, SyntaxTreesToString(compiler.Compilation));
				}
			}
		}

		/// <summary>
		///     Gets a string containing the contents of all syntax tress of the <paramref name="compilation" />.
		/// </summary>
		/// <param name="compilation">The compilation whose syntax trees should be written to a string.</param>
		protected static string SyntaxTreesToString(Compilation compilation)
		{
			var builder = new StringBuilder();

			foreach (var syntaxTree in compilation.SyntaxTrees)
			{
				builder.AppendLine();
				builder.AppendLine();
				builder.AppendLine("=============================================");
				builder.AppendLine(Path.GetFileName(syntaxTree.FilePath));
				builder.AppendLine("=============================================");
				builder.AppendLine(syntaxTree.ToString());
			}

			return builder.ToString();
		}

		/// <summary>
		///     Appends <paramref name="diagnostic" /> to the <paramref name="builder" />.
		/// </summary>
		/// <param name="builder">The builder the diagnostic should be appended to.</param>
		/// <param name="diagnostic">The diagnostic that should be appended.</param>
		public static void Write(StringBuilder builder, Diagnostic diagnostic)
		{
			var lineSpan = diagnostic.Location.GetLineSpan();
			var message = diagnostic.ToString();
			message = message.Substring(message.IndexOf(":", StringComparison.InvariantCulture) + 1);

			builder.AppendFormat("({1}-{2}) {0}\n\n", message, lineSpan.StartLinePosition, lineSpan.EndLinePosition);
		}

		/// <summary>
		///     Fails the test with the explanatory <paramref name="message" />.
		/// </summary>
		/// <param name="message">The explanatory format message.</param>
		/// <param name="args">The format arguments.</param>
		[StringFormatMethod("message")]
		protected static void Fail(string message, params object[] args)
		{
			throw new TestException(message, args);
		}

		/// <summary>
		///     Enumerates all C#-based test cases located at <paramref name="path" /> or any sub-directory.
		/// </summary>
		/// <param name="path">The path to the directory where C#-based tests are located.</param>
		protected static IEnumerable<object[]> EnumerateTestCases(string path)
		{
			var files = Directory.GetFiles(path, "*.cs", SearchOption.AllDirectories);

			foreach (var file in files.OrderBy(file => file))
			{
				var prefix = Path.GetDirectoryName(file).Substring(path.Length);
				var testName = String.IsNullOrWhiteSpace(prefix)
					? Path.GetFileNameWithoutExtension(file)
					: String.Format("[{0}] {1}", prefix.Substring(1), Path.GetFileNameWithoutExtension(file));
				var code = File.ReadAllText(file).Replace("\t", "    ");
				var syntaxTree = SyntaxFactory.ParseSyntaxTree(code, path: file, encoding: Encoding.UTF8);

				yield return new object[] { testName, syntaxTree };
			}
		}

		/// <summary>
		///     Checks that no exceptions escape unhandled during the execution of <paramref name="action" />.
		/// </summary>
		/// <param name="action">The action that should be checked.</param>
		protected static void NoThrow(Action action)
		{
			Requires.NotNull(action, () => action);

			try
			{
				action();
			}
			catch (Exception e)
			{
				var message = "Expected no exception to be thrown, but an exception of type '{0}' was raised:\n{1}";
				Fail(message, e.GetType().FullName, e.Message);
			}
		}

		/// <summary>
		///     Checks whether <paramref name="action" /> raises an exception of type <typeparamref name="T" /> satisfying the
		///     <paramref name="assertion" />.
		/// </summary>
		/// <typeparam name="T">The type of the exception that is expected to be thrown.</typeparam>
		/// <param name="action">The action that should be checked.</param>
		/// <param name="assertion">The assertion that should be checked on the thrown exception.</param>
		protected static void RaisesWith<T>(Action action, Action<T> assertion)
			where T : Exception
		{
			Requires.NotNull(action, () => action);

			Exception exception = null;

			try
			{
				action();
			}
			catch (Exception e)
			{
				exception = e;
			}

			if (exception == null)
				Fail("Expected an exception of type '{0}', but no exception was thrown.", typeof(T).FullName);

			var typedException = exception as T;
			if (typedException != null)
			{
				if (assertion != null)
					assertion(typedException);
			}
			else
			{
				var message = "Expected an exception of type '{0}', but an exception of type '{1}' was thrown instead.\n\nMessage:\n{2}";
				Fail(message, typeof(T).FullName, exception.GetType().FullName, exception.Message);
			}
		}

		/// <summary>
		///     Checks whether <paramref name="action" /> raises an exception of type <typeparamref name="T" />.
		/// </summary>
		/// <typeparam name="T">The type of the exception that is expected to be thrown.</typeparam>
		/// <param name="action">The action that should be checked.</param>
		protected static void Raises<T>(Action action)
			where T : Exception
		{
			RaisesWith<T>(action, null);
		}

		/// <summary>
		///     Checks whether <paramref name="action" /> raises an <see cref="InvalidOperationException" />.
		/// </summary>
		/// <param name="action">The action that should be checked.</param>
		protected static void RaisesInvalidOpException(Action action)
		{
			Raises<InvalidOperationException>(action);
		}
	}
}