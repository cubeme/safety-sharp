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
	using SafetySharp.Metamodel.Types;

	[TestFixture]
	internal class TypeSymbolExtensionsTests
	{
		private static void ShouldDeriveFrom(string csharpCode, string baseClassName, bool shouldDeriveFrom = true)
		{
			var compilation = new TestCompilation(csharpCode);
			var classSymbol = compilation.FindClassSymbol("X");
			var baseSymbol = compilation.FindClassSymbol(baseClassName);

			classSymbol.IsDerivedFrom(baseSymbol).Should().Be(shouldDeriveFrom);
		}

		private static void ShouldNotDeriveFrom(string csharpCode, string baseClassName)
		{
			ShouldDeriveFrom(csharpCode, baseClassName, false);
		}

		private static TypeSymbol ToTypeSymbol(string csharpCode)
		{
			var compilation = new TestCompilation(csharpCode);
			var fieldSymbol = compilation.FindFieldSymbol("X", "f");
			return fieldSymbol.Type.ToTypeSymbol(compilation.SemanticModel);
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