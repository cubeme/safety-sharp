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

namespace Tests.CSharp.Normalization
{
	using System;
	using System.Linq;
	using FluentAssertions;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using NUnit.Framework;
	using SafetySharp.CSharp.Extensions;
	using SafetySharp.CSharp.Normalization;

	[TestFixture]
	internal class StateFormulaNormalizerTests
	{
		private static string Normalize(string csharpExpression)
		{
			var compilation = new TestCompilation(@"
				class C1 
				{
					public bool value;
					public C1 c2;
				}

				enum TestEnum { A }				

				class X 
				{ 
					static bool _staticValue;
					LtlFormula M(int i) 
					{ 
						var value = true;
						var c1 = new C1 { value = false, c2 = new C1 { value = true }};
						return " + csharpExpression + @"; 
					}
				}");

			return new StateFormulaNormalizer()
				.Normalize(compilation.CSharpCompilation)
				.SyntaxTrees
				.Single()
				.DescendantNodes<ReturnStatementSyntax>()
				.Single()
				.Expression
				.ToString();
		}

		[Test]
		public void DoesNotRewriteRegularInvocations()
		{
			Normalize("M(1)").Should().Be("M(1)");
		}

		[Test]
		public void RewritesNestedStateFormulas()
		{
			Normalize("Ltl.Next(Ltl.Globally((1 == 2) != false))")
				.Should().Be("Ltl.Next(Ltl.Globally(global::SafetySharp.Modeling.Ltl.StateFormula(\"(1 == 2) != false\")))");

			Normalize("Ltl.Until(true, Ltl.Globally(false)")
				.Should().Be("Ltl.Until(global::SafetySharp.Modeling.Ltl.StateFormula(\"true\"), " +
							 "Ltl.Globally(global::SafetySharp.Modeling.Ltl.StateFormula(\"false\")))");
		}

		[Test]
		public void RewritesNonNestedStateFormulas()
		{
			Normalize("Ltl.Next((1 == 2) != false)")
				.Should().Be("Ltl.Next(global::SafetySharp.Modeling.Ltl.StateFormula(\"(1 == 2) != false\"))");

			Normalize("Ltl.Next(TestEnum.A == TestEnum.A)")
				.Should().Be("Ltl.Next(global::SafetySharp.Modeling.Ltl.StateFormula(\"TestEnum.A == TestEnum.A\"))");

			Normalize("Ltl.Next(_staticValue == X._staticValue)")
				.Should().Be("Ltl.Next(global::SafetySharp.Modeling.Ltl.StateFormula(\"{0} == {1}\", _staticValue, X._staticValue))");

			Normalize("Ltl.Next(c1.value == false)")
				.Should().Be("Ltl.Next(global::SafetySharp.Modeling.Ltl.StateFormula(\"{0}.value == false\"), c1)");

			Normalize("Ltl.Next(value == false)")
				.Should().Be("Ltl.Next(global::SafetySharp.Modeling.Ltl.StateFormula(\"{0} == false\"), value)");

			Normalize("Ltl.Next(c1.c2.value == false)")
				.Should().Be("Ltl.Next(Ltl.StateFormula(\"{0}.value == false\"), c1.c2)");

			Normalize("Ltl.Until(true, false)")
				.Should().Be("Ltl.Until(global::SafetySharp.Modeling.Ltl.StateFormula(\"true\"), " +
							 "global::SafetySharp.Modeling.Ltl.StateFormula(\"false\"))");
		}
	}
}