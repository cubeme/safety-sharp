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
				class C1 : Component
				{
					public bool value;
					public C1 c2;
				}

				enum TestEnum { A }				

				class X 
				{ 
					static bool _staticValue;
					bool _nonStaticValue;

					LtlFormula M(int i) 
					{ 
						var x = new X();
						var value = true;
						var c1 = new C1 { value = false, c2 = new C1 { value = true }};
						var accessInternal = c1.AccessInternal<bool>(""value"");
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
		public void RewritesComponentNonStaticFieldAccess()
		{
			Normalize("Ltl.Next(c1.value == false)")
				.Should().Be("Ltl.Next(global::SafetySharp.Modeling.Ltl.StateFormula(\"{0}.value == false\"), c1)");
		}

		[Test]
		public void RewritesConstants()
		{
			Normalize("Ltl.Next((1 == 2) != false)")
				.Should().Be("Ltl.Next(global::SafetySharp.Modeling.Ltl.StateFormula(\"(1 == 2) != false\"))");
		}

		[Test]
		public void RewritesEnumerationLiteralsStateFormula()
		{
			Normalize("Ltl.Next(TestEnum.A == TestEnum.A)")
				.Should().Be("Ltl.Next(global::SafetySharp.Modeling.Ltl.StateFormula(\"{0} == {1}\", TestEnum.A, TestEnum.A))");
		}

		[Test]
		public void RewritesLocalVariableAccesses()
		{
			Normalize("Ltl.Next(value == false)")
				.Should().Be("Ltl.Next(global::SafetySharp.Modeling.Ltl.StateFormula(\"{0} == false\"), value)");

			Normalize("Ltl.Next(accessInternal == false)")
				.Should().Be("Ltl.Next(global::SafetySharp.Modeling.Ltl.StateFormula(\"{0} == false\"), accessInternal)");
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
		public void RewritesNonComponentNonStaticFieldAccess()
		{
			Normalize("Ltl.Next(x._nonStaticValue == false)")
				.Should().Be("Ltl.Next(global::SafetySharp.Modeling.Ltl.StateFormula(\"{0} == false\"), x._nonStaticValue)");
		}

		[Test]
		public void RewritesStaticAccesses()
		{
			Normalize("Ltl.Next(_staticValue == X._staticValue)")
				.Should().Be("Ltl.Next(global::SafetySharp.Modeling.Ltl.StateFormula(\"{0} == {1}\", _staticValue, X._staticValue))");
		}

		[Test]
		public void RewritesSubComponentFieldAccess()
		{
			Normalize("Ltl.Next(c1.c2.value == false)")
				.Should().Be("Ltl.Next(global::SafetySharp.Modeling.Ltl.StateFormula(\"{0}.value == false\"), c1.c2)");
		}

		[Test]
		public void RewritesUntilFormula()
		{
			Normalize("Ltl.Until(true, false)")
				.Should().Be("Ltl.Until(global::SafetySharp.Modeling.Ltl.StateFormula(\"true\"), " +
							 "global::SafetySharp.Modeling.Ltl.StateFormula(\"false\"))");
		}
	}
}