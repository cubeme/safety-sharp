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

namespace Tests.CSharp.Diagnostics
{
	using System;
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.CSharp.Diagnostics;

	[TestFixture]
	internal class EnumMemberAnalyzerTests : CSharpAnalyzerTests<EnumMemberAnalyzer>
	{
		[Test]
		public void NoExplicitValuesShouldBeValid()
		{
			Validate("enum E { A, B, C }").Should().BeTrue();
		}

		[Test]
		public void ExplicitValueOnFirstMemberShouldBeInvalid()
		{
			Validate("enum E { A = 1, B, C }").Should().BeFalse();
		}

		[Test]
		public void ExplicitValueOnSecondMemberShouldBeInvalid()
		{
			Validate("enum E { A, B = 1, C }").Should().BeFalse();
		}

		[Test]
		public void ExplicitValueOnThirdMemberShouldBeInvalid()
		{
			Validate("enum E { A, B, C = 3 }").Should().BeFalse();
		}

		[Test]
		public void ExplicitValueOnAllMembersShouldBeInvalid()
		{
			Validate("enum E { A = 4, B = 1, C = 3 }").Should().BeFalse();
		}
	}
}