﻿// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
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

namespace Tests.Formulas
{
	using System;
	using System.Collections.Generic;
	using System.IO;
	using System.Text;
	using JetBrains.Annotations;
	using SafetySharp.Analysis;
	using SafetySharp.Runtime.Formulas;
	using Shouldly;
	using Utilities;
	using Xunit.Abstractions;

	public abstract class FormulaTestObject : TestObject
	{
		protected void Check(CtlFormula actual, Formula expected)
		{
			Check(actual.Formula, expected);
		}

		protected void Check(LtlFormula actual, Formula expected)
		{
			Check(actual.Formula, expected);
		}

		protected void Check(Formula actual, Formula expected)
		{
			var builder = new StringBuilder();
			builder.AppendLine("Actual:");
			builder.AppendLine(actual.ToString());
			builder.AppendLine();

			builder.AppendLine("Expected:");
			builder.AppendLine(expected.ToString());

			Output.Log("{0}", builder.ToString());

			actual.IsStructurallyEquivalent(expected).ShouldBe(true);
		}
	}

	partial class FormulaTests : Tests
	{
		public FormulaTests(ITestOutputHelper output)
			: base(output)
		{
		}

		[UsedImplicitly]
		public static IEnumerable<object[]> DiscoverTests(string directory)
		{
			return EnumerateTestCases(Path.Combine(Path.GetDirectoryName(GetFileName()), directory));
		}
	}
}