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

namespace Tests
{
	using System;
	using System.Linq;
	using FluentAssertions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.MSBuild;
	using NUnit.Framework;

	[TestFixture]
	public class CSharpTests
	{
		[Test]
		public void Test()
		{
			var code = @"
using SafetySharp.Modeling;

public class BooleanComponent : Component
{
	private bool _value;
	
	public BooleanComponent()
	{
		_value = Choose(true, false);
	}

	protected override void Update()
	{
		_value = Choose(true, false);
	}
}
";
			var parsed = CSharpSyntaxTree.ParseText(code);
			parsed.GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>().Count().Should().Be(1);

			var ws = MSBuildWorkspace.Create();
			var r = ws.OpenProjectAsync(@"D:\Projects\SafetySharp\Source\Models\Elbtunnel\Elbtunnel.csproj").Result;
			return;

			//var ws = new CustomWorkspace();
			//var info = new ProjectInfo(ProjectId.CreateNewId(), new VersionStamp(), "Test", "Test.dll", "CSharp", null, null, new CSharpCompilationOptions(), new CSharpParseOptions(), , )
			//var proj = ws.AddProject(info);
			//ws.Get

			//var solutionId = SolutionId.CreateNewId();
			//ProjectId projectId;
			//DocumentId documentId;
			//var solution = Solution.Create(solutionId)
			//	.AddCSharpProject("MyProject", "MyProject", out projectId)
			//	.AddMetadataReference(projectId, MetadataReference.CreateAssemblyReference("mscorlib"))
			//	.AddDocument(projectId, "MyFile.cs", source, out documentId);
			//var document = solution.GetDocument(documentId);
			//var model = (SemanticModel)document.GetSemanticModel();
		}
	}
}