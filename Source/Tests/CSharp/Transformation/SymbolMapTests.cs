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

namespace Tests.CSharp.Transformation
{
	using System;

	namespace SymbolMapTests
	{
		using FluentAssertions;
		using NUnit.Framework;
		using SafetySharp.CSharp.Transformation;
		using SafetySharp.Metamodel;
		using SafetySharp.Metamodel.Declarations;

		internal class SymbolMapTests
		{
			protected TestCompilation _compilation;
			protected SymbolMap _symbolMap;

			protected void Compile(string csharpCode)
			{
				_compilation = new TestCompilation(csharpCode);
				_symbolMap = new SymbolMap(_compilation.CSharpCompilation);
			}
		}

		[TestFixture]
		internal class IsMappedMethod : SymbolMapTests
		{
			private bool IsComponentMapped(string componentName)
			{
				return _symbolMap.IsMapped(_compilation.FindClassSymbol(componentName));
			}

			private bool IsInterfaceMapped(string interfaceName)
			{
				return _symbolMap.IsMapped(_compilation.FindInterfaceSymbol(interfaceName));
			}

			private bool IsFieldMapped(string className, string fieldName)
			{
				return _symbolMap.IsMapped(_compilation.FindFieldSymbol(className, fieldName));
			}

			private bool IsMethodMapped(string className, string methodName)
			{
				return _symbolMap.IsMapped(_compilation.FindMethodSymbol(className, methodName));
			}

			[Test]
			public void ReturnsFalseForFieldsOfNonComponentClass()
			{
				Compile("class X { int x; }");
				IsFieldMapped("X", "x").Should().BeFalse();
			}

			[Test]
			public void ReturnsFalseForMethodsOfNonComponentClass()
			{
				Compile("class X { void M() {} }");
				IsMethodMapped("X", "M").Should().BeFalse();
			}

			[Test]
			public void ReturnsFalseForNonComponentClass()
			{
				Compile("class X {}");
				IsComponentMapped("X").Should().BeFalse();

				Compile("class Y {} class X : Y {}");
				IsComponentMapped("X").Should().BeFalse();
				IsComponentMapped("Y").Should().BeFalse();
			}

			[Test]
			public void ReturnsFalseForNonComponentInterface()
			{
				Compile("interface X {}");
				IsInterfaceMapped("X").Should().BeFalse();

				Compile("interface Y {} interface X : Y {}");
				IsInterfaceMapped("X").Should().BeFalse();
				IsInterfaceMapped("Y").Should().BeFalse();
			}

			[Test]
			public void ReturnsFalseForSubComponentFields()
			{
				Compile("class X : Component { Component c1; IComponent c2; }");
				IsFieldMapped("X", "c1").Should().BeFalse();
				IsFieldMapped("X", "c2").Should().BeFalse();

				Compile("class Y : Component {} interface Z : IComponent {} class X : Component { Z c1; Y c2; }");
				IsFieldMapped("X", "c1").Should().BeFalse();
				IsFieldMapped("X", "c2").Should().BeFalse();
			}

			[Test]
			public void ReturnsTrueForComponentClass()
			{
				Compile("class X : Component {}");
				IsComponentMapped("X").Should().BeTrue();

				Compile("class Y : Component {} class X : Y {}");
				IsComponentMapped("X").Should().BeTrue();
				IsComponentMapped("Y").Should().BeTrue();
			}

			[Test]
			public void ReturnsTrueForComponentInterface()
			{
				Compile("interface X : IComponent {}");
				IsInterfaceMapped("X").Should().BeTrue();

				Compile("interface Y : IComponent {} interface X : Y {}");
				IsInterfaceMapped("X").Should().BeTrue();
				IsInterfaceMapped("Y").Should().BeTrue();
			}

			[Test]
			public void ReturnsTrueForFieldsOfComponentClass()
			{
				Compile("class X : Component { int x; }");
				IsFieldMapped("X", "x").Should().BeTrue();

				Compile("class Y : Component {} class X : Y { int x; }");
				IsFieldMapped("X", "x").Should().BeTrue();
			}

			[Test]
			public void ReturnsTrueForMethodsOfComponentClass()
			{
				Compile("class X : Component { void M() {} }");
				IsMethodMapped("X", "M").Should().BeTrue();

				Compile("class Y : Component {} class X : Y { void M() {} }");
				IsMethodMapped("X", "M").Should().BeTrue();
			}
		}

		[TestFixture]
		internal class GetComponentReferenceMethod : SymbolMapTests
		{
			private IMetamodelReference<ComponentDeclaration> GetReference(string componentName)
			{
				return _symbolMap.GetComponentReference(_compilation.FindClassSymbol(componentName));
			}

			[Test]
			public void ReturnsDifferentReferencesForDifferentComponents()
			{
				Compile("class Y : Component {} class X : Y {} class Z : Component {}");
				var referenceX = GetReference("X");
				var referenceY = GetReference("Y");
				var referenceZ = GetReference("Z");

				referenceX.Should().NotBe(referenceY);
				referenceX.Should().NotBe(referenceZ);
				referenceY.Should().NotBe(referenceZ);
			}

			[Test]
			public void ReturnsReferenceForComponent()
			{
				Compile("class X : Component {}");
				GetReference("X").Should().NotBeNull();

				Compile("class Y : Component {} class X : Y {}");
				GetReference("X").Should().NotBeNull();
				GetReference("Y").Should().NotBeNull();
			}

			[Test]
			public void ReturnsTheSameReferenceForTheSameComponent()
			{
				Compile("class Y : Component {} class X : Y {}");

				var reference = GetReference("X");
				reference.Should().Be(GetReference("X"));
			}

			[Test]
			public void ThrowsForNonComponentSymbols()
			{
				Compile("class Y {} class X : Y {}");
				Action action = () => GetReference("X");
				action.ShouldThrow<InvalidOperationException>();

				action = () => GetReference("Y");
				action.ShouldThrow<InvalidOperationException>();
			}
		}

		[TestFixture]
		internal class GetInterfaceReferenceMethod : SymbolMapTests
		{
			private IMetamodelReference<InterfaceDeclaration> GetReference(string interfaceName)
			{
				return _symbolMap.GetInterfaceReference(_compilation.FindInterfaceSymbol(interfaceName));
			}

			[Test]
			public void ReturnsDifferentReferencesForDifferentComponentInterfaces()
			{
				Compile("interface Y : IComponent {} interface X : Y {} interface Z : IComponent {}");
				var referenceX = GetReference("X");
				var referenceY = GetReference("Y");
				var referenceZ = GetReference("Z");

				referenceX.Should().NotBe(referenceY);
				referenceX.Should().NotBe(referenceZ);
				referenceY.Should().NotBe(referenceZ);
			}

			[Test]
			public void ReturnsReferenceForComponentInterface()
			{
				Compile("interface X : IComponent {}");
				GetReference("X").Should().NotBeNull();

				Compile("interface Y : IComponent {} interface X : Y {}");
				GetReference("X").Should().NotBeNull();
				GetReference("Y").Should().NotBeNull();
			}

			[Test]
			public void ReturnsTheSameReferenceForTheSameComponentInterface()
			{
				Compile("interface Y : IComponent {} interface X : Y {}");

				var reference = GetReference("X");
				reference.Should().Be(GetReference("X"));
			}

			[Test]
			public void ThrowsForNonComponentInterfaceSymbols()
			{
				Compile("interface Y {} interface X : Y {}");
				Action action = () => GetReference("X");
				action.ShouldThrow<InvalidOperationException>();

				action = () => GetReference("Y");
				action.ShouldThrow<InvalidOperationException>();
			}
		}

		[TestFixture]
		internal class GetFieldReferenceMethod : SymbolMapTests
		{
			private IMetamodelReference<FieldDeclaration> GetReference(string className, string fieldName)
			{
				return _symbolMap.GetFieldReference(_compilation.FindFieldSymbol(className, fieldName));
			}

			[Test]
			public void ReturnsDifferentReferencesForDifferentFields()
			{
				Compile("class X : Component { int x; int y; } class Y : Component { int x; }");
				var reference1 = GetReference("X", "x");
				var reference2 = GetReference("X", "y");
				var reference3 = GetReference("Y", "x");

				reference1.Should().NotBe(reference2);
				reference1.Should().NotBe(reference3);
				reference2.Should().NotBe(reference3);
			}

			[Test]
			public void ReturnsReferenceForFieldsOfComponent()
			{
				Compile("class X : Component { int x; }");
				GetReference("X", "x").Should().NotBeNull();

				Compile("class X : Component { int x; bool b; }");
				GetReference("X", "x").Should().NotBeNull();
				GetReference("X", "b").Should().NotBeNull();
			}

			[Test]
			public void ReturnsTheSameReferenceForTheSameField()
			{
				Compile("class X : Component { int x; }");

				var reference = GetReference("X", "x");
				reference.Should().Be(GetReference("X", "x"));
			}

			[Test]
			public void ThrowsForFieldsOfNonComponentSymbols()
			{
				Compile("class Y { int y; } class X : Y { int x; }");
				Action action = () => GetReference("X", "x");
				action.ShouldThrow<InvalidOperationException>();

				action = () => GetReference("Y", "y");
				action.ShouldThrow<InvalidOperationException>();
			}

			[Test]
			public void ThrowsForSubComponentFields()
			{
				Compile("class X : Component { Component c1; IComponent c2; }");

				Action action = () => GetReference("X", "c1");
				action.ShouldThrow<InvalidOperationException>();

				action = () => GetReference("X", "c2");
				action.ShouldThrow<InvalidOperationException>();

				Compile("class Y : Component {} interface Z : IComponent {} class X : Component { Z c1; Y c2; }");

				action = () => GetReference("X", "c1");
				action.ShouldThrow<InvalidOperationException>();

				action = () => GetReference("X", "c2");
				action.ShouldThrow<InvalidOperationException>();
			}
		}

		[TestFixture]
		internal class GetMethodReferenceMethod : SymbolMapTests
		{
			private IMetamodelReference<MethodDeclaration> GetReference(string className, string methodName)
			{
				return _symbolMap.GetMethodReference(_compilation.FindMethodSymbol(className, methodName));
			}

			[Test]
			public void ReturnsDifferentReferencesForDifferentMethods()
			{
				Compile("class X : Component { void M() {} void N() {} } class Y : Component { void M() {} }");
				var reference1 = GetReference("X", "M");
				var reference2 = GetReference("X", "N");
				var reference3 = GetReference("Y", "M");

				reference1.Should().NotBe(reference2);
				reference1.Should().NotBe(reference3);
				reference2.Should().NotBe(reference3);
			}

			[Test]
			public void ReturnsReferenceForMethodsOfComponent()
			{
				Compile("class X : Component { void M() {} }");
				GetReference("X", "M").Should().NotBeNull();

				Compile("class X : Component { void M() {} void N() {} }");
				GetReference("X", "M").Should().NotBeNull();
				GetReference("X", "N").Should().NotBeNull();
			}

			[Test]
			public void ReturnsTheSameReferenceForTheSameMethod()
			{
				Compile("class X : Component { void M() {} }");

				var reference = GetReference("X", "M");
				reference.Should().Be(GetReference("X", "M"));
			}

			[Test]
			public void ThrowsForMethodsOfNonComponentSymbols()
			{
				Compile("class Y { void M() {} } class X : Y { void N() {} }");
				Action action = () => GetReference("X", "N");
				action.ShouldThrow<InvalidOperationException>();

				action = () => GetReference("Y", "M");
				action.ShouldThrow<InvalidOperationException>();
			}
		}
	}
}