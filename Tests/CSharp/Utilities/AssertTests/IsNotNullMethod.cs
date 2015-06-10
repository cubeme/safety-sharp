// The MIT License (MIT)
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

namespace Tests.Utilities.AssertTests
{
	using System;
	using Shouldly;
	using Utilities;
	using Xunit;
	using Assert = SafetySharp.Utilities.Assert;

	public class IsNotNullMethod : Tests
	{
		[Fact]
		public void ThrowsIfObjIsNull()
		{
			RaisesWith(
				() => Assert.NotNull((object)null, "null: {0}", 1),
				(NullReferenceException e) => e.Message.ShouldBe("null: 1"));

			RaisesWith(
				() => Assert.NotNull((object)null),
				(NullReferenceException e) => e.Message.ShouldBe("Unexpected 'null'."));
		}

		[Fact]
		public void DoesNotThrowIfObjIsNotNull()
		{
			NoThrow(() => Assert.NotNull(new object()));
		}
	}
}