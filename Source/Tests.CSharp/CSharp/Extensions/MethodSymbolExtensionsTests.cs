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

	namespace MethodSymbolExtensionsTests
	{
		using System.Linq;
		using FluentAssertions;
		using Microsoft.CodeAnalysis;
		using Microsoft.CodeAnalysis.CSharp;
		using Microsoft.CodeAnalysis.CSharp.Syntax;
		using NUnit.Framework;
		using SafetySharp.CSharp.Extensions;

		[TestFixture]
		internal class OverridesMethod
		{
			private static bool Overrides(string csharpCode)
			{
				var compilation = new TestCompilation("class Y { public virtual void M() {} }" + csharpCode);
				var methodSymbol = compilation.FindMethodSymbol("X", "M");
				var overridenMethodSymbol = compilation.FindMethodSymbol("Y", "M");

				return methodSymbol.Overrides(overridenMethodSymbol);
			}

			[Test]
			public void ReturnsFalseForNonOverridingMethod()
			{
				Overrides("class X : Y { public new void M() {} }").Should().BeFalse();
				Overrides("class X : Y { public virtual new void M() {} }").Should().BeFalse();
				Overrides("class X { public virtual void M() {} }").Should().BeFalse();
			}

			[Test]
			public void ReturnsTrueForOverridingMethod()
			{
				Overrides("class X : Y { public override void M() {} }").Should().BeTrue();
				Overrides("class X : Y { public sealed override void M() {} }").Should().BeTrue();
				Overrides("class Z : Y {} class X : Z { public override void M () {} }").Should().BeTrue();
				Overrides("class Z : Y { public override void M() {} } class X : Z { public override void M () {} }").Should().BeTrue();
			}
		}

		[TestFixture]
		internal class GetFullNameMethod
		{
			private static string GetFullName(string csharpCode)
			{
				var compilation = new TestCompilation(csharpCode);
				var typeDeclaration = compilation
					.SyntaxRoot
					.DescendantNodesAndSelf<TypeDeclarationSyntax>()
					.Single(c => c.Identifier.ValueText == "X");

				var typeSymbol = compilation.SemanticModel.GetDeclaredSymbol(typeDeclaration);
				return typeSymbol.GetMembers().OfType<IMethodSymbol>().Single(method => method.Name == "M").GetFullName();
			}

			[Test]
			public void ReturnsMethodNameForGenericMethod()
			{
				GetFullName("class X { T1 M<T1>(int t1, T1 t2) { return default(T1); } }").Should().Be("T1 X.M<T1>(System.Int32, T1)");
				GetFullName("class X { T1 M<T1, T2>(T1 t1, T2 t2) { return default(T1); } }").Should().Be("T1 X.M<T1, T2>(T1, T2)");
			}

			[Test]
			public void ReturnsMethodNameForGenericMethodOfGenericType()
			{
				GetFullName("class X<T1> { T1 M<T2>(int t1, T2 t2) { return default(T1); } }").Should().Be("T1 X<T1>.M<T2>(System.Int32, T2)");
				GetFullName("struct X<T1> { T3 M<T2, T3>(T2 t1, T3 t2) { return default(T3); } }").Should().Be("T3 X<T1>.M<T2, T3>(T2, T3)");
			}

			[Test]
			public void ReturnsMethodNameForGenericType()
			{
				GetFullName("class X<T1, T2> { int M(int i) { return i; } }").Should().Be("System.Int32 X<T1, T2>.M(System.Int32)");
				GetFullName("class X<T1, T2> { T1 M(T1 t1, T2 t2) { return default(T1); } }").Should().Be("T1 X<T1, T2>.M(T1, T2)");
			}

			[Test]
			public void ReturnsMethodNameForInterfaceMethod()
			{
				GetFullName("interface X { int M(); }").Should().Be("System.Int32 X.M()");
				GetFullName("interface X { float M(); }").Should().Be("System.Single X.M()");
				GetFullName("class Y {} interface X { Y M(); }").Should().Be("Y X.M()");
			}

			[Test]
			public void ReturnsMethodNameForMethodWithParameters()
			{
				GetFullName("class X { void M(int a) { } }").Should().Be("System.Void X.M(System.Int32)");
				GetFullName("class X { void M(int a, int b) { } }").Should().Be("System.Void X.M(System.Int32, System.Int32)");
				GetFullName("class X { void M(int a, int[] b) { } }").Should().Be("System.Void X.M(System.Int32, System.Int32[])");
				GetFullName("class X { void M(int a, params int[] b) { } }").Should().Be("System.Void X.M(System.Int32, System.Int32[])");
				GetFullName("class X { void M(int a, int[,,] b) { } }").Should().Be("System.Void X.M(System.Int32, System.Int32[,,])");
				GetFullName("namespace Q { struct Z {} } class X { void M(ref Q.Z z) { } }").Should().Be("System.Void X.M(ref Q.Z)");
				GetFullName("namespace Q { struct Z {} } class X { void M(out Q.Z z) { z = new Q.Z(); } }").Should().Be("System.Void X.M(out Q.Z)");
			}

			[Test]
			public void ReturnsMethodNameForNestedType()
			{
				GetFullName("class Y { class X { int M(int i) { return i; } }}").Should().Be("System.Int32 Y+X.M(System.Int32)");
				GetFullName("namespace Test.Other { class Y { class X { int M(int i) { return i; } }} }")
					.Should().Be("System.Int32 Test.Other.Y+X.M(System.Int32)");
				GetFullName("namespace Test { namespace Other { class Y { class X { int M(int i) { return i; } }} }}")
					.Should().Be("System.Int32 Test.Other.Y+X.M(System.Int32)");
				GetFullName("namespace Test { class Y { class X { int M(int i) { return i; } }} }").Should().Be("System.Int32 Test.Y+X.M(System.Int32)");
			}

			[Test]
			public void ReturnsMethodNameForParameterlessMethod()
			{
				GetFullName("class X { int M() { return 0; } }").Should().Be("System.Int32 X.M()");
				GetFullName("class X { float M() { return 0; } }").Should().Be("System.Single X.M()");
				GetFullName("class Y {} class X { Y M() { return null; } }").Should().Be("Y X.M()");
			}

			[Test]
			public void ReturnsMethodNameForTypeInNamespace()
			{
				GetFullName("namespace Test { class X { int M(int i) { return i; } } }").Should().Be("System.Int32 Test.X.M(System.Int32)");
				GetFullName("namespace Test.Other { class X { int M(int i) { return i; } } }").Should().Be("System.Int32 Test.Other.X.M(System.Int32)");
				GetFullName("namespace Test { namespace Other { class X { int M(int i) { return i; } } }}")
					.Should().Be("System.Int32 Test.Other.X.M(System.Int32)");
			}
		}
	}
}