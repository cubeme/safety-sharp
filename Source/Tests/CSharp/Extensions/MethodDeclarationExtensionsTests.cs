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

namespace Tests.CSharp.Extensions
{
	using System;

	namespace MethodsDeclarationExtensionsTests
	{
		using FluentAssertions;
		using NUnit.Framework;
		using SafetySharp.CSharp.Extensions;

		[TestFixture]
		internal class IsUpdateMethodMethod
		{
			private static bool IsUpdateMethod(string csharpCode, string methodName = "Update")
			{
				var compilation = new TestCompilation(csharpCode);
				var methodDeclaration = compilation.FindMethodDeclaration("X", methodName);
				return methodDeclaration.IsUpdateMethod(compilation.SemanticModel);
			}

			[Test]
			public void ReturnsFalseIfMethodDoesNotOverrideUpdate()
			{
				IsUpdateMethod("class X : Component { public new void Update() {} }").Should().BeFalse();
			}

			[Test]
			public void ReturnsFalseIfMethodIsNotUpdate()
			{
				IsUpdateMethod("class X : Component { public void M() {} }", methodName: "M").Should().BeFalse();
			}

			[Test]
			public void ReturnsTrueIfMethodOverridesUpdate()
			{
				IsUpdateMethod("class X : Component { protected override void Update() {} }").Should().BeTrue();
				IsUpdateMethod("class Y : Component {} class X : Y { protected override void Update() {} }").Should().BeTrue();
				IsUpdateMethod("class Y : Component { protected override void Update() {}} class X : Y { protected override void Update() {} }")
					.Should().BeTrue();
			}
		}
	}
}