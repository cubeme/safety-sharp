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

namespace Tests.CSharp
{
	using System;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using SafetySharp.Metamodel;

	/// <summary>
	///     Represents a compiled C# compilation unit with a single syntax tree.
	/// </summary>
	internal class TestCompilation
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="csharpCode">The C# code that should be compiled.</param>
		public TestCompilation(string csharpCode)
		{
			var compilationUnit = SyntaxFactory.ParseCompilationUnit(csharpCode);
			SyntaxTree = compilationUnit.SyntaxTree;

			Compilation = CSharpCompilation.Create("Test")
										   .AddReferences(new MetadataFileReference(typeof(object).Assembly.Location))
										   .AddReferences(new MetadataFileReference(typeof(MetamodelElement).Assembly.Location))
										   .AddSyntaxTrees(SyntaxTree);

			SemanticModel = Compilation.GetSemanticModel(SyntaxTree);
			SyntaxRoot = SyntaxTree.GetRoot();
		}

		/// <summary>
		///     Gets the C# compilation.
		/// </summary>
		public CSharpCompilation Compilation { get; private set; }

		/// <summary>
		///     Gets the syntax tree of the compilation.
		/// </summary>
		public SyntaxTree SyntaxTree { get; private set; }

		/// <summary>
		///     Gets the root syntax node of the syntax tree.
		/// </summary>
		public SyntaxNode SyntaxRoot { get; private set; }

		/// <summary>
		///     Gets the semantic model for the compilation's syntax tree.
		/// </summary>
		public SemanticModel SemanticModel { get; private set; }
	}
}