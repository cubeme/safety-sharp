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

	namespace ArgumentExtensionsTests
	{
		using System.Linq;
		using FluentAssertions;
		using Microsoft.CodeAnalysis;
		using Microsoft.CodeAnalysis.CSharp.Syntax;
		using NUnit.Framework;
		using SafetySharp.CSharp.Extensions;
		using SafetySharp.Modeling;
		using SafetySharp.Utilities;

		internal class ArgumentExtensionsTests
		{
			protected InvocationExpressionSyntax[] _invocations;
			protected IMethodSymbol _methodM;
			protected IMethodSymbol _methodN;
			protected SemanticModel _semanticModel;

			[SetUp]
			public void Setup()
			{
				var compilation = new TestCompilation(@"
					class X
					{
						public void M(int a, [StateFormula] int b, int c)
						{
						}

						public void N(int a, [StateFormula] params int[] b)
						{
						}

						public X()
						{
							M(1, 2, 3 + 4);
							N(1, 2, 3, 4);
							M(c: 5, a: 1, b: 3);
						}
					}");

				_methodM = compilation.FindMethodSymbol("X", "M");
				_methodN = compilation.FindMethodSymbol("X", "N");

				_invocations = compilation.SyntaxRoot.DescendantNodes<InvocationExpressionSyntax>().ToArray();
				_semanticModel = compilation.SemanticModel;
			}
		}

		[TestFixture]
		internal class ParameterHasAttributeMethod : ArgumentExtensionsTests
		{
			private bool ParameterHasAttribute<T>(int invocationIndex, int argumentIndex)
			{
				return _invocations[invocationIndex].ArgumentList.Arguments[argumentIndex].ParameterHasAttribute<T>(_semanticModel);
			}

			[Test]
			public void ReturnsFalseWhenDifferentAttributeIsApplied()
			{
				ParameterHasAttribute<PureAttribute>(0, 0).Should().BeFalse();
				ParameterHasAttribute<PureAttribute>(0, 2).Should().BeFalse();

				ParameterHasAttribute<PureAttribute>(1, 0).Should().BeFalse();

				ParameterHasAttribute<PureAttribute>(2, 0).Should().BeFalse();
				ParameterHasAttribute<PureAttribute>(2, 2).Should().BeFalse();
			}

			[Test]
			public void ReturnsFalseWhenNoAttributeIsApplied()
			{
				ParameterHasAttribute<StateFormulaAttribute>(0, 0).Should().BeFalse();
				ParameterHasAttribute<StateFormulaAttribute>(0, 2).Should().BeFalse();

				ParameterHasAttribute<StateFormulaAttribute>(1, 0).Should().BeFalse();

				ParameterHasAttribute<StateFormulaAttribute>(2, 0).Should().BeFalse();
				ParameterHasAttribute<StateFormulaAttribute>(2, 1).Should().BeFalse();
			}

			[Test]
			public void ReturnsTrueWhenAttributeIsApplied()
			{
				ParameterHasAttribute<StateFormulaAttribute>(0, 1).Should().BeTrue();

				ParameterHasAttribute<StateFormulaAttribute>(1, 1).Should().BeTrue();
				ParameterHasAttribute<StateFormulaAttribute>(1, 2).Should().BeTrue();
				ParameterHasAttribute<StateFormulaAttribute>(1, 3).Should().BeTrue();

				ParameterHasAttribute<StateFormulaAttribute>(2, 2).Should().BeTrue();
			}

			[Test]
			public void ThrowsWhenArgumentIsNull()
			{
				Action action = () => ArgumentExtensions.ParameterHasAttribute<StateFormulaAttribute>(null, _semanticModel);
				action.ShouldThrow<ArgumentNullException>();
			}

			[Test]
			public void ThrowsWhenSemanticModelIsNull()
			{
				Action action = () => _invocations[0].ArgumentList.Arguments[0].ParameterHasAttribute<StateFormulaAttribute>(null);
				action.ShouldThrow<ArgumentNullException>();
			}
		}

		[TestFixture]
		internal class GetMethodSymbolMethod : ArgumentExtensionsTests
		{
			private void CheckMethodSymbol(int invocationIndex, int argumentIndex, IMethodSymbol expectedMethodSymbol)
			{
				var actualMethodSymbol = _invocations[invocationIndex].ArgumentList.Arguments[argumentIndex].GetMethodSymbol(_semanticModel);
				actualMethodSymbol.Should().Be(expectedMethodSymbol);
			}

			[Test]
			public void ReturnsCorrectMethodSymbol()
			{
				CheckMethodSymbol(0, 0, _methodM);
				CheckMethodSymbol(0, 1, _methodM);
				CheckMethodSymbol(0, 2, _methodM);

				CheckMethodSymbol(1, 0, _methodN);
				CheckMethodSymbol(1, 1, _methodN);
				CheckMethodSymbol(1, 2, _methodN);
				CheckMethodSymbol(1, 3, _methodN);

				CheckMethodSymbol(2, 0, _methodM);
				CheckMethodSymbol(2, 1, _methodM);
				CheckMethodSymbol(2, 2, _methodM);
			}

			[Test]
			public void ThrowsWhenArgumentIsNull()
			{
				Action action = () => ArgumentExtensions.GetMethodSymbol(null, _semanticModel);
				action.ShouldThrow<ArgumentNullException>();
			}

			[Test]
			public void ThrowsWhenSemanticModelIsNull()
			{
				Action action = () => _invocations[0].ArgumentList.Arguments[0].GetMethodSymbol(null);
				action.ShouldThrow<ArgumentNullException>();
			}
		}
	}
}