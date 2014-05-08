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
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.CSharp.Extensions;

	[TestFixture]
	internal class TypeDeclarationExtensionsTests
	{
		private static void ShouldBeComponent(string csharpCode, bool shouldBeComponent = true)
		{
			var compilation = new TestCompilation(csharpCode);
			var classDeclaration = compilation.FindClassDeclaration("X");
			classDeclaration.IsComponentDeclaration(compilation.SemanticModel).Should().Be(shouldBeComponent);
		}

		private static void ShouldNotBeComponent(string csharpCode)
		{
			ShouldBeComponent(csharpCode, false);
		}

		private static void ShouldBeComponentInterface(string csharpCode, bool shouldBeComponent = true)
		{
			var compilation = new TestCompilation(csharpCode);
			var interfaceDeclaration = compilation.FindInterfaceDeclaration("X");
			interfaceDeclaration.IsComponentInterfaceDeclaration(compilation.SemanticModel).Should().Be(shouldBeComponent);
		}

		private static void ShouldNotBeComponentInterface(string csharpCode)
		{
			ShouldBeComponentInterface(csharpCode, false);
		}

		[Test]
		public void IsComponentInterfaceDeclaration_False_NonComponentInterface()
		{
			ShouldNotBeComponentInterface("interface X {}");
		}

		[Test]
		public void IsComponentInterfaceDeclaration_False_NonComponentInterface_OtherBase()
		{
			ShouldNotBeComponentInterface("interface Y {} interface X : Y {}");
		}

		[Test]
		public void IsComponentInterfaceDeclaration_True_DirectBase_First()
		{
			ShouldBeComponentInterface("interface Y {} interface X : IComponent, Y {}");
		}

		[Test]
		public void IsComponentInterfaceDeclaration_True_DirectBase_Second()
		{
			ShouldBeComponentInterface("interface Y {} interface X : Y, IComponent {}");
		}

		[Test]
		public void IsComponentInterfaceDeclaration_True_IndirectBase_Second()
		{
			ShouldBeComponentInterface("interface Q{} interface Z : Q, IComponent {} interface Y : Z {} interface X : Y {}");
		}

		[Test]
		public void IsComponentInterfaceDeclaration_True_IndirectBase_First()
		{
			ShouldBeComponentInterface("interface Q{} interface Z : IComponent, Q {} interface Y : Z {} interface X : Y {}");
		}

		[Test]
		public void IsComponentDeclaration_False_NonComponentClassWithBase()
		{
			ShouldNotBeComponent("class Y {} class X : Y {}");
		}

		[Test]
		public void IsComponentDeclaration_False_NonDerivedNonComponentClass()
		{
			ShouldNotBeComponent("class X {}");
		}

		[Test]
		public void IsComponentDeclaration_True_DirectComponentClass()
		{
			ShouldBeComponent("class X : SafetySharp.Modeling.Component {}");
		}

		[Test]
		public void IsComponentDeclaration_True_DirectComponentClassWithUsing()
		{
			ShouldBeComponent("using SafetySharp.Modeling; class X : Component {}");
		}

		[Test]
		public void IsComponentDeclaration_True_NonDirectComponentClass()
		{
			ShouldBeComponent("class Y : SafetySharp.Modeling.Component {} class X : Y {}");
		}

		[Test]
		public void IsComponentDeclaration_True_NonDirectComponentClassWithUsing()
		{
			ShouldBeComponent("using SafetySharp.Modeling; class Y : Component {} class X : Y {}");
		}
	}
}