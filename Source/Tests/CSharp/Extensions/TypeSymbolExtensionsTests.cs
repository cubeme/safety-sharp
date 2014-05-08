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

	namespace TypeSymbolExtensionsTests
	{
		using FluentAssertions;
		using NUnit.Framework;
		using SafetySharp.CSharp.Extensions;
		using SafetySharp.Metamodel.Types;

		[TestFixture]
		internal class IsDerivedFromMethod
		{
			private static bool IsDerivedFrom(string csharpCode, string baseName)
			{
				var compilation = new TestCompilation(csharpCode);
				var derivedSymbol = compilation.FindTypeSymbol("X");
				var baseSymbol = compilation.FindTypeSymbol(baseName);

				return derivedSymbol.IsDerivedFrom(baseSymbol);
			}

			[Test]
			public void ReturnsFalseForSelfChecks()
			{
				IsDerivedFrom("interface X {}", "X").Should().BeFalse();
				IsDerivedFrom("class X {}", "X").Should().BeFalse();
			}

			[Test]
			public void ReturnsFalseWhenClassNotDerivedFromBaseClass()
			{
				IsDerivedFrom("class Q {} class X {}", "Q").Should().BeFalse();
				IsDerivedFrom("class Q {} class Y {} class X : Y {}", "Q").Should().BeFalse();
				IsDerivedFrom("class Q {} class Z {} class Y : Z {} class X : Y {}", "Q").Should().BeFalse();
			}

			[Test]
			public void ReturnsFalseWhenInterfaceNotDerivedFromBaseInterface()
			{
				IsDerivedFrom("interface Q {} interface X {}", "Q").Should().BeFalse();
				IsDerivedFrom("interface Q {} interface Y {} interface X : Y {}", "Q").Should().BeFalse();
				IsDerivedFrom("interface Q {} interface Z {} interface Y : Z {} interface X : Y {}", "Q").Should().BeFalse();
			}

			[Test]
			public void ReturnsTrueWhenClassDerivesFromBaseClass()
			{
				IsDerivedFrom("class Y {} class X : Y {}", "Y").Should().BeTrue();
				IsDerivedFrom("class Z {} class Y : Z {} class X : Y {}", "Y").Should().BeTrue();
				IsDerivedFrom("class Z {} class Y : Z {} class X : Y {}", "Z").Should().BeTrue();
			}

			[Test]
			public void ReturnsTrueWhenClassHasBaseDerivedFromBaseInterface()
			{
				IsDerivedFrom("interface Q {} interface Z {} class Y : Z, Q {} class X : Y {}", "Q").Should().BeTrue();
				IsDerivedFrom("interface Q {} interface Z {} class Y : Z, Q {} class X : Y {}", "Z").Should().BeTrue();
				IsDerivedFrom("interface S {} interface Q {} class Z : Q, S {} class Y : Z, Q {} class X : Y {}", "Q").Should().BeTrue();
				IsDerivedFrom("interface S {} interface Q {} class Z : Q, S {} class Y : Z, Q {} class X : Y {}", "S").Should().BeTrue();
			}

			[Test]
			public void ReturnsTrueWhenInterfaceDerivesFromBaseInterface()
			{
				IsDerivedFrom("interface Y {} interface X : Y {}", "Y").Should().BeTrue();
				IsDerivedFrom("interface Z {} interface Y : Z {} interface X : Y {}", "Y").Should().BeTrue();
				IsDerivedFrom("interface Z {} interface Y : Z {} interface X : Y {}", "Z").Should().BeTrue();
				IsDerivedFrom("interface Z {} interface Y : Z {} interface X : Y, Z {}", "Y").Should().BeTrue();
				IsDerivedFrom("interface Z {} interface Y : Z {} interface X : Y, Z {}", "Z").Should().BeTrue();
				IsDerivedFrom("interface Z {} interface Y {} interface X : Y, Z {}", "Y").Should().BeTrue();
				IsDerivedFrom("interface Z {} interface Y {} interface X : Y, Z {}", "Z").Should().BeTrue();
				IsDerivedFrom("interface Q {} interface Z {} interface Y : Z, Q {} interface X : Y {}", "Q").Should().BeTrue();
			}
		}

		[TestFixture]
		internal class ToTypeSymbolMethod
		{
			private static TypeSymbol ToTypeSymbol(string csharpCode)
			{
				var compilation = new TestCompilation(csharpCode);
				var fieldSymbol = compilation.FindFieldSymbol("X", "f");
				return fieldSymbol.Type.ToTypeSymbol(compilation.SemanticModel);
			}

			[Test]
			public void ReturnsBooleanTypeSymbolForBooleanField()
			{
				ToTypeSymbol("class X { bool f; }").Should().Be(TypeSymbol.Boolean);
			}

			[Test]
			public void ReturnsDecimalTypeSymbolForDecimalField()
			{
				ToTypeSymbol("class X { decimal f; }").Should().Be(TypeSymbol.Decimal);
			}

			[Test]
			public void ReturnsIntegerTypeSymbolForIntegerField()
			{
				ToTypeSymbol("class X { int f; }").Should().Be(TypeSymbol.Integer);
			}
		}
	}
}