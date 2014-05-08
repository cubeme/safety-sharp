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
	using Microsoft.CodeAnalysis;
	using NUnit.Framework;
	using SafetySharp.CSharp.Extensions;
	using SafetySharp.Metamodel.Types;

	[TestFixture]
	internal class TypeSymbolExtensionsTests
	{
		private static void CheckBases(string csharpCode, string baseName, Func<ITypeSymbol, ITypeSymbol, bool> func, bool shouldHaveBase)
		{
			var compilation = new TestCompilation(csharpCode);
			var derivedSymbol = compilation.FindTypeSymbol("X");
			var baseSymbol = compilation.FindTypeSymbol(baseName);

			func(derivedSymbol, baseSymbol).Should().Be(shouldHaveBase);
		}

		private static void ShouldDeriveFrom(string csharpCode, string baseName)
		{
			CheckBases(csharpCode, baseName, (d, b) => d.IsDerivedFrom(b), true);
		}

		private static void ShouldNotDeriveFrom(string csharpCode, string baseName)
		{
			CheckBases(csharpCode, baseName, (d, b) => d.IsDerivedFrom(b), false);
		}

		private static void ShouldImplement(string csharpCode, string baseName)
		{
			CheckBases(csharpCode, baseName, (d, b) => d.Implements(b), true);
		}

		private static void ShouldNotImplement(string csharpCode, string baseName)
		{
			CheckBases(csharpCode, baseName, (d, b) => d.Implements(b), false);
		}

		private static TypeSymbol ToTypeSymbol(string csharpCode)
		{
			var compilation = new TestCompilation(csharpCode);
			var fieldSymbol = compilation.FindFieldSymbol("X", "f");
			return fieldSymbol.Type.ToTypeSymbol(compilation.SemanticModel);
		}

		[Test]
		public void Implements_False_UnderivedBaseType_HasBase()
		{
			ShouldNotImplement("interface Q {} interface Y {} interface X : Y {}", "Q");
		}

		[Test]
		public void Implements_False_UnderivedBaseType_NoBase()
		{
			ShouldNotImplement("interface Q {} interface X {}", "Q");
		}

		[Test]
		public void Implements_False_UnderivedBaseType_TwoBases()
		{
			ShouldNotImplement("interface Q {} interface Z {} interface Y : Z {} interface X : Y {}", "Q");
		}

		[Test]
		public void Implements_ShouldThrow_WhenBaseIsClass()
		{
			Action action = () => ShouldImplement("class Y {} class X : Y {}", "Y");
			action.ShouldThrow<ArgumentException>();
		}

		[Test]
		public void Implements_True_BaseBaseClassImplementsInterface_First()
		{
			ShouldImplement("interface S {} interface Q {} class Z : Q, S {} class Y : Z, Q {} class X : Y {}", "Q");
		}

		[Test]
		public void Implements_True_BaseBaseClassImplementsInterface_Second()
		{
			ShouldImplement("interface S {} interface Q {} class Z : Q, S {} class Y : Z, Q {} class X : Y {}", "S");
		}

		[Test]
		public void Implements_True_BaseClassImplementsInterface_First()
		{
			ShouldImplement("interface Q {} interface Z {} class Y : Z, Q {} class X : Y {}", "Z");
		}

		[Test]
		public void Implements_True_BaseClassImplementsInterface_Second()
		{
			ShouldImplement("interface Q {} interface Z {} class Y : Z, Q {} class X : Y {}", "Q");
		}

		[Test]
		public void Implements_True_BaseIsNotTopLevel()
		{
			ShouldImplement("interface Z {} interface Y : Z {} interface X : Y {}", "Y");
		}

		[Test]
		public void Implements_True_BaseIsTwoLevelsUp()
		{
			ShouldImplement("interface Z {} interface Y : Z {} interface X : Y {}", "Y");
		}

		[Test]
		public void Implements_True_DirectBase()
		{
			ShouldImplement("interface Y {} interface X : Y {}", "Y");
		}

		[Test]
		public void Implements_True_FirstBase()
		{
			ShouldImplement("interface Z {} interface Y : Z {} interface X : Y, Z {}", "Y");
		}

		[Test]
		public void Implements_True_SecondBase()
		{
			ShouldImplement("interface Z {} interface Y : Z {} interface X : Y, Z {}", "Z");
		}

		[Test]
		public void Implements_True_SecondBaseOfBaseInterface()
		{
			ShouldImplement("interface Q {} interface Z {} interface Y : Z, Q {} interface X : Y {}", "Q");
		}

		[Test]
		public void IsDerivedFrom_False_UnderivedBaseTypeWhenClassHasBase()
		{
			ShouldNotDeriveFrom("class Q {} class Y {} class X : Y {}", "Q");
		}

		[Test]
		public void IsDerivedFrom_False_UnderivedBaseTypeWhenClassHasNoBase()
		{
			ShouldNotDeriveFrom("class Q {} class X {}", "Q");
		}

		[Test]
		public void IsDerivedFrom_False_UnderivedBaseTypeWhenClassHasTwoBases()
		{
			ShouldNotDeriveFrom("class Q {} class Z {} class Y : Z {} class X : Y {}", "Q");
		}

		[Test]
		public void IsDerivedFrom_ShouldThrow_WhenBaseIsInterface()
		{
			Action action = () => ShouldDeriveFrom("interface Y {} class X : Y {}", "Y");
			action.ShouldThrow<ArgumentException>();
		}

		[Test]
		public void IsDerivedFrom_True_BaseIsNotTopLevel()
		{
			ShouldDeriveFrom("class Z {} class Y : Z {} class X : Y {}", "Y");
		}

		[Test]
		public void IsDerivedFrom_True_BaseIsTwoLevelsUp()
		{
			ShouldDeriveFrom("class Z {} class Y : Z {} class X : Y {}", "Y");
		}

		[Test]
		public void IsDerivedFrom_True_DirectBase()
		{
			ShouldDeriveFrom("class Y {} class X : Y {}", "Y");
		}

		[Test]
		public void ToTypeSymbol_Boolean()
		{
			ToTypeSymbol("class X { bool f; }").Should().Be(TypeSymbol.Boolean);
		}

		[Test]
		public void ToTypeSymbol_Decimal()
		{
			ToTypeSymbol("class X { decimal f; }").Should().Be(TypeSymbol.Decimal);
		}

		[Test]
		public void ToTypeSymbol_Integer()
		{
			ToTypeSymbol("class X { int f; }").Should().Be(TypeSymbol.Integer);
		}
	}
}