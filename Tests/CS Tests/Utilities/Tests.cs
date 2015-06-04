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
	using System.Linq;
	using System.Runtime.CompilerServices;
	using System.Text;
	using Diagnostics;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using SafetySharp.Compiler.Normalization;
	using SafetySharp.CSharp.Analyzers;
	using SafetySharp.CSharp.Utilities;
	using SafetySharp.Modeling;
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
		public Tests(ITestOutputHelper output)
		{
			Requires.NotNull(output, () => output);
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
		///     Creates a compilation for the <paramref name="compilationUnits" />.
		/// </summary>
		/// <param name="compilationUnits">The compilation units the compilation should contain.</param>
		protected static Compilation CreateCompilation(params string[] compilationUnits)
		{
			var compilation = CSharpCompilation
				.Create("Test")
				.WithOptions(new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary))
				.AddSyntaxTrees(compilationUnits.Select(unit => SyntaxFactory.ParseSyntaxTree(unit)))
				.AddReferences(MetadataReference.CreateFromAssembly(typeof(object).Assembly))
				.AddReferences(MetadataReference.CreateFromAssembly(typeof(DynamicAttribute).Assembly))
				.AddReferences(MetadataReference.CreateFromAssembly(typeof(Component).Assembly))
				.AddReferences(MetadataReference.CreateFromAssembly(typeof(DiagnosticAttribute).Assembly))
				.AddReferences(MetadataReference.CreateFromAssembly(typeof(DiagnosticIdentifier).Assembly))
				.AddReferences(MetadataReference.CreateFromAssembly(typeof(BindingNormalizer).Assembly));

			var errors = compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error).ToArray();
			if (errors.Length == 0)
				return compilation;

			var builder = new StringBuilder();

			foreach (var diagnostic in errors)
				Write(builder, diagnostic);

			throw new CSharpException("\n\nFailed to create compilation:\n\n" + builder);
		}

		/// <summary>
		///     Appends <paramref name="diagnostic" /> to the <paramref name="builder" />.
		/// </summary>
		/// <param name="builder">The builder the diagnostic should be appended to.</param>
		/// <param name="diagnostic">The diagnostic that should be appended.</param>
		protected static void Write(StringBuilder builder, Diagnostic diagnostic)
		{
			var lineSpan = diagnostic.Location.GetLineSpan();
			var message = diagnostic.ToString();
			message = message.Substring(message.IndexOf(":", StringComparison.InvariantCulture) + 1);

			builder.AppendFormat("({1}-{2}) {0}\n\n", message, lineSpan.StartLinePosition, lineSpan.EndLinePosition);
		}

		/// <summary>
		///     Raised when invalid C# code is detected or compilation of a dynamic C# project failed.
		/// </summary>
		private class CSharpException : Exception
		{
			/// <summary>
			///     Initializes a new instance.
			/// </summary>
			/// <param name="message">The format message of the exception.</param>
			/// <param name="args">The format arguments.</param>
			[StringFormatMethod("message")]
			public CSharpException(string message, params object[] args)
				: base(String.Format(message, args))
			{
			}
		}
	}
}