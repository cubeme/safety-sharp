﻿// The MIT License (MIT)
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

namespace Tests.Normalization
{
	using System;
	using System.Collections.Generic;
	using System.IO;
	using System.Linq;
	using System.Text;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using SafetySharp.CSharp.Roslyn;
	using SafetySharp.CSharp.Roslyn.Syntax;
	using Utilities;
	using Xunit.Abstractions;

	internal class SyntaxNodeComparer : IEqualityComparer<BaseTypeDeclarationSyntax>
	{
		public bool Equals(BaseTypeDeclarationSyntax x, BaseTypeDeclarationSyntax y)
		{
			return x.IsEquivalentTo(y, topLevel: false);
		}

		public int GetHashCode(BaseTypeDeclarationSyntax obj)
		{
			return 0;
		}
	}

	public partial class NormalizationTests
	{
		public NormalizationTests(ITestOutputHelper output)
			: base(output)
		{
		}

		private void CheckNormalization<T>(string code)
			where T : Normalizer, new()
		{
			var syntaxTree = SyntaxFactory.ParseSyntaxTree(code);

			// Ensure that there are no errors
			CreateCompilation(syntaxTree);

			// Extract the inputs and outputs
			var inputs = syntaxTree.Descendants<BaseTypeDeclarationSyntax>().Where(t => t.Identifier.ValueText.StartsWith("In")).ToArray();
			var expectedOutputs = syntaxTree.Descendants<BaseTypeDeclarationSyntax>().Where(t => t.Identifier.ValueText.StartsWith("Out")).ToArray();

			if (inputs.Length == 0)
				throw new TestException("Expected a type declaration with an identifier starting with 'In'.");

			// Remove the outputs from the input code
			var root = syntaxTree.GetRoot();
			var inputCode = root.RemoveNodes(expectedOutputs, SyntaxRemoveOptions.KeepNoTrivia);

			// Create a compilation for the inputs and check for any errors
			var compilation = CreateCompilation(SyntaxFactory.SyntaxTree(inputCode));
			CheckForSSharpDiagnostics(compilation);

			// Create the expected outputs; if the normalization does nothing, the inputs also act as the expected outputs
			var renamer = new Renamer();
			expectedOutputs = expectedOutputs.Length == 0
				? inputs
				: expectedOutputs.Select(t => (BaseTypeDeclarationSyntax)t.Accept(renamer)).ToArray();

			// Normalize the input
			var normalizer = new T();
			compilation = normalizer.Normalize(compilation);

			// Compare the results
			var actualOutputs = compilation
				.SyntaxTrees
				.SelectMany(t => t.Descendants<BaseTypeDeclarationSyntax>())
				.Where(t => t.Identifier.ValueText.StartsWith("In"))
				.ToArray();
			var commonOutput = expectedOutputs.Intersect(actualOutputs, new SyntaxNodeComparer());

			if (actualOutputs.Length == expectedOutputs.Length && actualOutputs.Length == commonOutput.Count())
				return;

			var builder = new StringBuilder();
			builder.AppendLine();
			builder.AppendLine();

			builder.AppendLine("Actual Outputs:");
			builder.AppendLine("===============");

			foreach (var declaration in actualOutputs)
				builder.AppendLine(declaration.NormalizeWhitespace().ToFullString());

			builder.AppendLine("Expected Outputs:");
			builder.AppendLine("=================");

			foreach (var declaration in expectedOutputs)
				builder.AppendLine(declaration.NormalizeWhitespace().ToFullString());

			throw new TestException("{0}", builder);
		}

		[UsedImplicitly]
		public static IEnumerable<object[]> DiscoverTests(string directory)
		{
			return EnumerateTestCases(Path.Combine(Path.GetDirectoryName(GetFileName()), directory));
		}

		private class Renamer : CSharpSyntaxRewriter
		{
			public override SyntaxNode VisitClassDeclaration(ClassDeclarationSyntax node)
			{
				if (!node.Identifier.ValueText.StartsWith("Out"))
					return base.VisitClassDeclaration(node);

				return ((ClassDeclarationSyntax)base.VisitClassDeclaration(node)).WithIdentifier(Rename(node.Identifier));
			}

			public override SyntaxNode VisitInterfaceDeclaration(InterfaceDeclarationSyntax node)
			{
				if (!node.Identifier.ValueText.StartsWith("Out"))
					return base.VisitInterfaceDeclaration(node);

				return ((InterfaceDeclarationSyntax)base.VisitInterfaceDeclaration(node)).WithIdentifier(Rename(node.Identifier));
			}

			public override SyntaxNode VisitStructDeclaration(StructDeclarationSyntax node)
			{
				if (!node.Identifier.ValueText.StartsWith("Out"))
					return base.VisitStructDeclaration(node);

				return ((StructDeclarationSyntax)base.VisitStructDeclaration(node)).WithIdentifier(Rename(node.Identifier));
			}

			public override SyntaxNode VisitDelegateDeclaration(DelegateDeclarationSyntax node)
			{
				if (!node.Identifier.ValueText.StartsWith("Out"))
					return base.VisitDelegateDeclaration(node);

				return ((DelegateDeclarationSyntax)base.VisitDelegateDeclaration(node)).WithIdentifier(Rename(node.Identifier));
			}

			public override SyntaxNode VisitEnumDeclaration(EnumDeclarationSyntax node)
			{
				if (!node.Identifier.ValueText.StartsWith("Out"))
					return base.VisitEnumDeclaration(node);

				return ((EnumDeclarationSyntax)base.VisitEnumDeclaration(node)).WithIdentifier(Rename(node.Identifier));
			}

			private SyntaxToken Rename(SyntaxToken identifier)
			{
				return SyntaxFactory.Identifier(identifier.ValueText.Replace("Out", "In")).WithTriviaFrom(identifier);
			}
		}
	}
}