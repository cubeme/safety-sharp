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

namespace Tests.Execution.Faults.ProvidedPorts
{
	using System;
	using SafetySharp.CompilerServices;
	using SafetySharp.Modeling.Faults;
	using Shouldly;
	using Utilities;

	internal class X10 : TestComponent
	{
		private int M()
		{
			return 1;
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Faults[0].Fault.IsOccurring = true;
			M().ShouldBe(1);
		}

		[Persistent]
		private class F : Fault<X10>
		{
			public int M()
			{
				return Component.M();
			}
		}
	}

	internal class X11 : TestComponent
	{
		private int M()
		{
			return 1;
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Faults[0].Fault.IsOccurring = true;
			Metadata.Faults[1].Fault.IsOccurring = true;
			M().ShouldBe(1);
		}

		[Persistent]
		private class F1 : Fault<X11>
		{
			public int M()
			{
				return Component.M();
			}
		}

		[Persistent]
		private class F2 : Fault<X11>
		{
			public int M()
			{
				return Component.M();
			}
		}
	}
}