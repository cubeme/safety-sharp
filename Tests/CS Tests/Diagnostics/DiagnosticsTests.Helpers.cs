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

namespace Tests.Diagnostics
{
	using System;
	using System.Collections.Generic;
	using System.Collections.Immutable;
	using System.IO;
	using System.Linq;
	using System.Text;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Microsoft.CodeAnalysis.Text;
	using SafetySharp.CSharp.Analyzers;
	using SafetySharp.CSharp.Roslyn;
	using SafetySharp.CSharp.Roslyn.Symbols;
	using SafetySharp.CSharp.Roslyn.Syntax;
	using Xunit.Abstractions;

	public class DiagnosticAttribute : Attribute
	{
		[UsedImplicitly]
		public DiagnosticAttribute(DiagnosticIdentifier id, int line, int column, int length, params string[] arguments)
		{
		}
	}

	public class DiagnosticComparer : IEqualityComparer<Diagnostic>
	{
		public bool Equals(Diagnostic x, Diagnostic y)
		{
			return x.Location == y.Location && x.ToString() == y.ToString();
		}

		public int GetHashCode(Diagnostic obj)
		{
			return obj.GetHashCode();
		}
	}

	public partial class DiagnosticsTests
	{
		public DiagnosticsTests(ITestOutputHelper output)
			: base(output)
		{
		}

		private void CheckDiagnostics(string code, Analyzer analyzer)
		{
			var compilation = CreateCompilation(code).WithAnalyzers(ImmutableArray.Create((DiagnosticAnalyzer)analyzer));

			var expectedDiagnostics = GetExpectedDiagnostics(analyzer, compilation.Compilation).ToArray();
			var actualDiagnostics = compilation.GetAllDiagnosticsAsync().Result.Where(d => !d.Descriptor.Id.StartsWith("CS")).ToArray();
			var commonDiagnostics = expectedDiagnostics.Intersect(actualDiagnostics, new DiagnosticComparer()).Count();

			if (expectedDiagnostics.Length != actualDiagnostics.Length || expectedDiagnostics.Length != commonDiagnostics)
			{
				var builder = new StringBuilder();
				builder.AppendLine();
				builder.AppendLine();
				builder.AppendLine("Actual Diagnostics:");
				builder.AppendLine("===================");

				foreach (var diagnostic in actualDiagnostics.OrderBy(d => d.Location.SourceSpan.Start))
					Write(builder, diagnostic);

				builder.AppendLine("Expected Diagnostics:");
				builder.AppendLine("=====================");

				foreach (var diagnostic in expectedDiagnostics.OrderBy(d => d.Location.SourceSpan.Start))
					Write(builder, diagnostic);

				throw new Exception(builder.ToString());
			}

			foreach (var diagnostic in actualDiagnostics)
				Log("{0}\n", diagnostic);
		}

		private static IEnumerable<Diagnostic> GetExpectedDiagnostics(Analyzer analyzer, Compilation compilation)
		{
			foreach (var syntaxTree in compilation.SyntaxTrees)
			{
				var semanticModel = compilation.GetSemanticModel(syntaxTree);

				foreach (var typeDeclaration in syntaxTree.Descendants<BaseTypeDeclarationSyntax>())
				{
					var symbol = typeDeclaration.GetTypeSymbol(semanticModel);
					var attribute = symbol.GetAttributes<DiagnosticAttribute>(semanticModel).FirstOrDefault();

					if (attribute == null)
						continue;

					var id = (DiagnosticIdentifier)attribute.ConstructorArguments[0].Value;
					var line = (int)attribute.ConstructorArguments[1].Value;
					var column = (int)attribute.ConstructorArguments[2].Value;
					var length = (int)attribute.ConstructorArguments[3].Value;
					var arguments = attribute.ConstructorArguments[4].Values.Select(v => v.Value).ToArray();

					var start = syntaxTree.GetText().Lines[line - 1].Start + column - 1;
					var location = Location.Create(syntaxTree, new TextSpan(start, length));

					yield return analyzer.GetDiagnosticInfo(id).CreateDiagnostic(location, arguments);
				}
			}
		}

		[UsedImplicitly]
		public static IEnumerable<object[]> DiscoverTests(string directory)
		{
			var files = Directory.GetFiles(Path.Combine(Path.GetDirectoryName(GetFileName()), directory));

			foreach (var file in files)
			{
				var testName = Path.GetFileNameWithoutExtension(file);
				var code = File.ReadAllText(file).Replace("\t", "    ");

				yield return new object[] { testName, code };
			}
		}
	}
}