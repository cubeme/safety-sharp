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

namespace Tests.CSharp.Normalization
{
	using System;
	using System.Linq;
	using FluentAssertions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using NUnit.Framework;
	using SafetySharp.CSharp.Extensions;
	using SafetySharp.CSharp.Normalization;

	[TestFixture]
	internal class TypesNormalizerTests
	{
		private static SyntaxNode Normalize(string csharpCode)
		{
			var compilation = new TestCompilation(csharpCode);

			var normalizer = new TypesNormalizer();
			return normalizer.Normalize(compilation.CSharpCompilation).SyntaxTrees.Single().GetRoot();
		}

		private static void Test<T>(string csharpCode, Func<T, string> identifier, bool shouldContain, string[] typeNames)
			where T : MemberDeclarationSyntax
		{
			Normalize("using SafetySharp.Modeling;" + csharpCode)
				.DescendantNodesAndSelf<T>()
				.Any(declaration => typeNames.Any(name => identifier(declaration) == name))
				.Should()
				.Be(shouldContain);
		}

		private static void ShouldContain<T>(string csharpCode, params string[] typeNames)
			where T : BaseTypeDeclarationSyntax
		{
			Test<T>(csharpCode, declaration => declaration.Identifier.ValueText, true, typeNames);
		}

		private static void ShouldNotContain<T>(string csharpCode, params string[] typeNames)
			where T : BaseTypeDeclarationSyntax
		{
			Test<T>(csharpCode, declaration => declaration.Identifier.ValueText, false, typeNames);
		}

		private static void ShouldNotContainDelegate(string csharpCode, params string[] typeNames)
		{
			// Unfortunately, DelegateDeclarationSyntax is not derived from BaseTypeDeclarationSyntax
			Test<DelegateDeclarationSyntax>(csharpCode, declaration => declaration.Identifier.ValueText, false, typeNames);
		}

		[Test]
		public void ShouldNotRemove_MultipleComponents()
		{
			ShouldContain<ClassDeclarationSyntax>(@"class X : Component {} class Y : Component {} class Z : Component {}", "X", "Y", "Z");
		}

		[Test]
		public void ShouldNotRemove_SingleComponent()
		{
			ShouldContain<ClassDeclarationSyntax>(@"class X : Component {}", "X");
		}

		[Test]
		public void ShouldRemove_Class()
		{
			ShouldNotContain<ClassDeclarationSyntax>("class Test{}", "Test");
		}

		[Test]
		public void ShouldRemove_Class_ShouldNotRemove_Component()
		{
			const string csharpCode = "class Test {} class X : Component {}";
			ShouldContain<ClassDeclarationSyntax>(csharpCode, "X");
			ShouldNotContain<ClassDeclarationSyntax>(csharpCode, "Test");
		}

		[Test]
		public void ShouldRemove_Delegate()
		{
			ShouldNotContainDelegate("delegate void Test();", "Test");
		}

		[Test]
		public void ShouldRemove_Interface()
		{
			ShouldNotContain<InterfaceDeclarationSyntax>("interface ITest{}", "ITest");
		}

		[Test]
		public void ShouldRemove_Struct()
		{
			ShouldNotContain<StructDeclarationSyntax>("struct Test{}", "Test");
		}
	}
}