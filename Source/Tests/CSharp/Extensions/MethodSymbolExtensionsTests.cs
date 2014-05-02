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
	internal class MethodSymbolExtensionsTests
	{
		private static void ShouldOverride(string csharpCode, bool shouldOverride = true)
		{
			var compilation = new TestCompilation("class Y { public virtual void M() {} }" + csharpCode);
			var methodSymbol = compilation.FindMethodSymbol("X", "M");
			var overridenMethodSymbol = compilation.FindMethodSymbol("Y", "M");

			methodSymbol.Overrides(overridenMethodSymbol).Should().Be(shouldOverride);
		}

		private static void ShouldNotOverride(string csharpCode)
		{
			ShouldOverride(csharpCode, false);
		}

		[Test]
		public void Overrides_False_NewMethod()
		{
			ShouldNotOverride("class X : Y { public new void M() {} }");
		}

		[Test]
		public void Overrides_False_NewVirtualMethod()
		{
			ShouldNotOverride("class X : Y { public virtual new void M() {} }");
		}

		[Test]
		public void Overrides_False_NoBaseType()
		{
			ShouldNotOverride("class X { public virtual void M() {} }");
		}

		[Test]
		public void Overrides_True_VirtualDirectBase()
		{
			ShouldOverride("class X : Y { public override void M() {} }");
		}

		[Test]
		public void Overrides_True_Sealed_AbstractDirectBase()
		{
			ShouldOverride("class X : Y { public sealed override void M() {} }");
		}

		[Test]
		public void Overrides_True_Sealed_VirtualDirectBase()
		{
			ShouldOverride("class X : Y { public sealed override void M() {} }");
		}

		[Test]
		public void Overrides_True_NotDirectBase_NoOverload()
		{
			ShouldOverride("class Z : Y {} class X : Y { public override void M () {} }");
		}

		[Test]
		public void Overrides_True_NotDirectBase_OverloadedTwice()
		{
			ShouldOverride("class Z : Y { public override void M() {} } class X : Y { public override void M () {} }");
		}
	}
}