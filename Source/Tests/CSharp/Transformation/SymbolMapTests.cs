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
	using System.Linq;
	using FluentAssertions;
	using Microsoft.CodeAnalysis;
	using NUnit.Framework;
	using SafetySharp.CSharp.Extensions;
	using SafetySharp.CSharp.Transformation;

	[TestFixture]
	internal class SymbolMapTests
	{
		private SymbolMap _symbolMap;
		private SyntaxNode _syntaxRoot;
		private SemanticModel _semanticModel;
		private TestCompilation _compilation;

		private void Compile(string csharpCode)
		{
			_compilation = new TestCompilation("using SafetySharp.Modeling; " + csharpCode);

			_semanticModel = _compilation.SemanticModel;
			_syntaxRoot = _compilation.SyntaxRoot;

			_symbolMap = new SymbolMap(_compilation.Compilation);
		}

		private ITypeSymbol GetClassSymbol(string className)
		{
			return _compilation.FindClassSymbol(className);
		}

		private ITypeSymbol GetInterfaceSymbol(string interfaceName)
		{
			return _compilation.FindInterfaceSymbol(interfaceName);
		}

		private static IMethodSymbol GetMethodSymbol(ITypeSymbol classSymbol, string methodName)
		{
			return classSymbol.GetMembers(methodName).OfType<IMethodSymbol>().Single();
		}

		private static IFieldSymbol GetFieldSymbol(ITypeSymbol classSymbol, string fieldName)
		{
			return classSymbol.GetMembers(fieldName).OfType<IFieldSymbol>().Single();
		}

		[Test]
		public void ComponentClassShouldBeMapped()
		{
			Compile("class X : SafetySharp.Modeling.Component {}");
			var classSymbol = GetClassSymbol("X");

			_symbolMap.IsMapped(classSymbol).Should().BeTrue();
			_symbolMap.GetComponentReference(classSymbol).Should().NotBeNull();
		}

		[Test]
		public void ComponentClassesShouldBeMappedAndDifferentReferences()
		{
			Compile("using SafetySharp.Modeling; class Y : Component {} class X : Y {} class Z : Component {}");
			var classSymbolX = GetClassSymbol("X");
			var classSymbolY = GetClassSymbol("Y");
			var classSymbolZ = GetClassSymbol("Z");

			_symbolMap.IsMapped(classSymbolX).Should().BeTrue();
			_symbolMap.IsMapped(classSymbolY).Should().BeTrue();
			_symbolMap.IsMapped(classSymbolZ).Should().BeTrue();

			var referenceX = _symbolMap.GetComponentReference(classSymbolX);
			var referenceY = _symbolMap.GetComponentReference(classSymbolY);
			var referenceZ = _symbolMap.GetComponentReference(classSymbolZ);

			referenceX.Should().NotBeNull();
			referenceY.Should().NotBeNull();
			referenceZ.Should().NotBeNull();

			referenceX.Should().NotBe(referenceY);
			referenceX.Should().NotBe(referenceZ);
			referenceZ.Should().NotBe(referenceY);
		}

		[Test]
		public void ComponentInterfaceShouldBeMapped()
		{
			Compile("interface X : SafetySharp.Modeling.IComponent {}");
			var interfaceSymbol = GetInterfaceSymbol("X");

			_symbolMap.IsMapped(interfaceSymbol).Should().BeTrue();
			_symbolMap.GetInterfaceReference(interfaceSymbol).Should().NotBeNull();
		}

		[Test]
		public void ComponentInterfacesShouldBeMappedAndDifferentReferences()
		{
			Compile("using SafetySharp.Modeling; interface Y : IComponent {} interface X : Y {} interface Z : IComponent {}");
			var interfaceSymbolX = GetInterfaceSymbol("X");
			var interfaceSymbolY = GetInterfaceSymbol("Y");
			var interfaceSymbolZ = GetInterfaceSymbol("Z");

			_symbolMap.IsMapped(interfaceSymbolX).Should().BeTrue();
			_symbolMap.IsMapped(interfaceSymbolY).Should().BeTrue();
			_symbolMap.IsMapped(interfaceSymbolZ).Should().BeTrue();

			var referenceX = _symbolMap.GetInterfaceReference(interfaceSymbolX);
			var referenceY = _symbolMap.GetInterfaceReference(interfaceSymbolY);
			var referenceZ = _symbolMap.GetInterfaceReference(interfaceSymbolZ);

			referenceX.Should().NotBeNull();
			referenceY.Should().NotBeNull();
			referenceZ.Should().NotBeNull();

			referenceX.Should().NotBe(referenceY);
			referenceX.Should().NotBe(referenceZ);
			referenceZ.Should().NotBe(referenceY);
		}

		[Test]
		public void SubComponentsShouldNotBeMapped()
		{
			Compile("class X : Component { Component c1; IComponent c2; }");
			var classSymbol = GetClassSymbol("X");
			var fieldSymbol1 = GetFieldSymbol(classSymbol, "c1");
			var fieldSymbol2 = GetFieldSymbol(classSymbol, "c2");

			_symbolMap.IsMapped(fieldSymbol1).Should().BeFalse();
			_symbolMap.IsMapped(fieldSymbol2).Should().BeFalse();
		}

		[Test]
		public void InheritedComponentClassShouldBeMapped()
		{
			Compile("class Y : SafetySharp.Modeling.Component {} class X : Y {}");
			var classSymbol = GetClassSymbol("X");

			_symbolMap.IsMapped(classSymbol).Should().BeTrue();
			_symbolMap.GetComponentReference(classSymbol).Should().NotBeNull();
		}

		[Test]
		public void InheritedComponentInterfaceShouldBeMapped()
		{
			Compile("interface Y : SafetySharp.Modeling.IComponent {} interface X : Y {}");
			var interfaceSymbol = GetInterfaceSymbol("X");

			_symbolMap.IsMapped(interfaceSymbol).Should().BeTrue();
			_symbolMap.GetInterfaceReference(interfaceSymbol).Should().NotBeNull();
		}

		[Test]
		public void MethodOfComponentClassShouldBeMapped()
		{
			Compile("class X : SafetySharp.Modeling.Component { void M() {} }");
			var classSymbol = GetClassSymbol("X");
			var methodSymbol = GetMethodSymbol(classSymbol, "M");

			_symbolMap.IsMapped(methodSymbol).Should().BeTrue();
			_symbolMap.GetMethodReference(methodSymbol).Should().NotBeNull();
		}

		[Test]
		public void MethodOfNonComponentClassShouldNotBeMapped()
		{
			Compile("class X { void M() {} }");
			var classSymbol = GetClassSymbol("X");
			var methodSymbol = GetMethodSymbol(classSymbol, "M");

			_symbolMap.IsMapped(methodSymbol).Should().BeFalse();
			Action getReference = () => _symbolMap.GetMethodReference(methodSymbol);
			getReference.ShouldThrow<InvalidOperationException>();
		}

		[Test]
		public void MethodsOfComponentClassShouldBeMapped()
		{
			Compile("class X : SafetySharp.Modeling.Component { void M() {} void N() {} }");
			var classSymbol = GetClassSymbol("X");
			var methodSymbolM = GetMethodSymbol(classSymbol, "M");
			var methodSymbolN = GetMethodSymbol(classSymbol, "N");

			_symbolMap.IsMapped(methodSymbolM).Should().BeTrue();
			_symbolMap.IsMapped(methodSymbolM).Should().BeTrue();

			var referenceM = _symbolMap.GetMethodReference(methodSymbolM);
			var referenceN = _symbolMap.GetMethodReference(methodSymbolN);

			referenceM.Should().NotBeNull();
			referenceN.Should().NotBeNull();

			referenceM.Should().NotBe(referenceN);
		}

		[Test]
		public void NonComponentClassShouldNotBeMapped()
		{
			Compile("class X {}");
			var classSymbol = GetClassSymbol("X");

			_symbolMap.IsMapped(classSymbol).Should().BeFalse();

			Action getReference = () => _symbolMap.GetComponentReference(classSymbol);
			getReference.ShouldThrow<InvalidOperationException>();
		}

		[Test]
		public void NonComponentInterfaceShouldNotBeMapped()
		{
			Compile("interface X {}");
			var interfaceSymbol = GetInterfaceSymbol("X");

			_symbolMap.IsMapped(interfaceSymbol).Should().BeFalse();

			Action getReference = () => _symbolMap.GetInterfaceReference(interfaceSymbol);
			getReference.ShouldThrow<InvalidOperationException>();
		}

		[Test]
		public void FieldOfNonComponentClassShouldNotBeMapped()
		{
			Compile("class X { int x; }");
			var classSymbol = GetClassSymbol("X");

			var fieldSymbol = GetFieldSymbol(classSymbol, "x");
			_symbolMap.IsMapped(fieldSymbol).Should().BeFalse();

			Action getReference = () => _symbolMap.GetFieldReference(fieldSymbol);
			getReference.ShouldThrow<InvalidOperationException>();
		}

		[Test]
		public void FieldOfComponentClassShouldBeMapped()
		{
			Compile("class X : Component { int x; }");
			var classSymbol = GetClassSymbol("X");
			var fieldSymbol = GetFieldSymbol(classSymbol, "x");

			_symbolMap.IsMapped(fieldSymbol).Should().BeTrue();
			_symbolMap.GetFieldReference(fieldSymbol).Should().NotBeNull();
		}

		[Test]
		public void FieldsOfComponentClassShouldBeMapped()
		{
			Compile("class X : Component { int x; bool y; }");
			var classSymbol = GetClassSymbol("X");
			var fieldSymbol1 = GetFieldSymbol(classSymbol, "x");
			var fieldSymbol2 = GetFieldSymbol(classSymbol, "y");

			_symbolMap.IsMapped(fieldSymbol1).Should().BeTrue();
			_symbolMap.IsMapped(fieldSymbol2).Should().BeTrue();

			_symbolMap.GetFieldReference(fieldSymbol1).Should().NotBeNull();
			_symbolMap.GetFieldReference(fieldSymbol2).Should().NotBeNull();
		}
	}
}