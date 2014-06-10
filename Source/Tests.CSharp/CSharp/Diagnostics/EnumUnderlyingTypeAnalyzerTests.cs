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
	internal class EnumUnderlyingTypeAnalyzerTests : CSharpAnalyzerTests<EnumUnderlyingTypeAnalyzer>
	{
		[Test]
		public void ByteAsUnderlyingTypeShouldBeInvalid()
		{
			Validate("enum E : byte { A }").Should().BeFalse();
		}

		[Test]
		public void ImplicitUnderlyingTypeShouldBeValid()
		{
			Validate("enum E { A }").Should().BeTrue();
		}

		[Test]
		public void IntUnderlyingTypeShouldBeInvalid()
		{
			Validate("enum E : int { A }").Should().BeFalse();
		}

		[Test]
		public void LongAsUnderlyingTypeShouldBeInvalid()
		{
			Validate("enum E : long { A }").Should().BeFalse();
		}

		[Test]
		public void SByteAsUnderlyingTypeShouldBeInvalid()
		{
			Validate("enum E : sbyte { A }").Should().BeFalse();
		}

		[Test]
		public void ShortAsUnderlyingTypeShouldBeInvalid()
		{
			Validate("enum E : short { A }").Should().BeFalse();
		}

		[Test]
		public void UIntAsUnderlyingTypeShouldBeInvalid()
		{
			Validate("enum E : uint { A }").Should().BeFalse();
		}

		[Test]
		public void ULongAsUnderlyingTypeShouldBeInvalid()
		{
			Validate("enum E : ulong { A }").Should().BeFalse();
		}

		[Test]
		public void UShortAsUnderlyingTypeShouldBeInvalid()
		{
			Validate("enum E : ushort { A }").Should().BeFalse();
		}
	}
}