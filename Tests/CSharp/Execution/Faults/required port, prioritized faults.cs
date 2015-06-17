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

namespace Tests.Execution.Faults
{
	using System;
	using SafetySharp.Modeling;
	using SafetySharp.Modeling.Faults;
	using Shouldly;
	using Utilities;

	internal class X4 : TestComponent
	{
		public X4()
		{
			Bind(RequiredPorts.M = ProvidedPorts.N);
		}

		private extern int M();

		private int N()
		{
			return 1;
		}

		protected override void Check()
		{
			Metadata.Faults[0].Fault.IsOccurring = false;
			Metadata.Faults[1].Fault.IsOccurring = false;

			M().ShouldBe(1);

			Metadata.Faults[0].Fault.IsOccurring = true;
			Metadata.Faults[1].Fault.IsOccurring = false;

			M().ShouldBe(2);

			Metadata.Faults[0].Fault.IsOccurring = false;
			Metadata.Faults[1].Fault.IsOccurring = true;

			M().ShouldBe(3);

			Metadata.Faults[0].Fault.IsOccurring = true;
			Metadata.Faults[1].Fault.IsOccurring = true;

			M().ShouldBe(3);
		}

		[Persistent]
		private class F1 : Fault<X4>
		{
			[Priority(1)]
			public int M()
			{
				return 2;
			}
		}

		[Persistent]
		private class F2 : Fault
		{
			[Priority(17)]
			public int M()
			{
				return 3;
			}
		}
	}
}