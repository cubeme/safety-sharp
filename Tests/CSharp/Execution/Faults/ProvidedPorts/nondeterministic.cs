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
	using System.Diagnostics;
	using SafetySharp.CompilerServices;
	using SafetySharp.Modeling.Faults;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal class X7 : TestComponent
	{
		private int M()
		{
			return -1;
		}

		[SuppressTransformation]
		protected override void Check()
		{
			var nondeterministicBehavior = (NondeterministicFaultInjection)Metadata.ProvidedPorts[0].Behaviors.FaultInjections[0];

			// N faults
			Metadata.Faults[0].Fault.IsOccurring = false;
			Metadata.Faults[1].Fault.IsOccurring = false;
			Metadata.Faults[2].Fault.IsOccurring = false;

			M().ShouldBe(-1);

			// One fault, deterministic
			Metadata.Faults[0].Fault.IsOccurring = true;
			Metadata.Faults[1].Fault.IsOccurring = false;
			Metadata.Faults[2].Fault.IsOccurring = false;

			M().ShouldBe(1);

			//
			Metadata.Faults[0].Fault.IsOccurring = false;
			Metadata.Faults[1].Fault.IsOccurring = true;
			Metadata.Faults[2].Fault.IsOccurring = false;

			M().ShouldBe(2);

			//
			Metadata.Faults[0].Fault.IsOccurring = false;
			Metadata.Faults[1].Fault.IsOccurring = false;
			Metadata.Faults[2].Fault.IsOccurring = true;

			M().ShouldBe(3);

			// Two faults, nondeterministic
			Metadata.Faults[0].Fault.IsOccurring = true;
			Metadata.Faults[1].Fault.IsOccurring = true;
			Metadata.Faults[2].Fault.IsOccurring = false;

			var result = M();
			(result == 1 || result == 2).ShouldBe(true);

			//
			Metadata.Faults[0].Fault.IsOccurring = true;
			Metadata.Faults[1].Fault.IsOccurring = false;
			Metadata.Faults[2].Fault.IsOccurring = true;

			result = M();
			(result == 1 || result == 3).ShouldBe(true);

			//
			Metadata.Faults[0].Fault.IsOccurring = false;
			Metadata.Faults[1].Fault.IsOccurring = true;
			Metadata.Faults[2].Fault.IsOccurring = true;

			result = M();
			(result == 3 || result == 2).ShouldBe(true);

			// Three faults, nondeterministic
			Metadata.Faults[0].Fault.IsOccurring = true;
			Metadata.Faults[1].Fault.IsOccurring = true;
			Metadata.Faults[2].Fault.IsOccurring = true;

			result = M();
			(result == 1 || result == 2 || result == 3).ShouldBe(true);

			//
			nondeterministicBehavior.ResetPriorityOverrides();
			nondeterministicBehavior.PriorityOverrides[0] = 17;
			nondeterministicBehavior.PriorityOverrides[1] = 17;

			result = M();
			(result == 1 || result == 2).ShouldBe(true);

			//
			nondeterministicBehavior.ResetPriorityOverrides();
			nondeterministicBehavior.PriorityOverrides[0] = 17;
			nondeterministicBehavior.PriorityOverrides[2] = 17;
	
			result = M();
			(result == 1 || result == 3).ShouldBe(true);

			//
			nondeterministicBehavior.ResetPriorityOverrides();
			nondeterministicBehavior.PriorityOverrides[2] = 17;
			nondeterministicBehavior.PriorityOverrides[1] = 17;

			result = M();
			(result == 3 || result == 2).ShouldBe(true);

			// Two faults, deterministic
			nondeterministicBehavior.ResetPriorityOverrides();
			Metadata.Faults[0].Fault.IsOccurring = true;
			Metadata.Faults[1].Fault.IsOccurring = true;
			Metadata.Faults[2].Fault.IsOccurring = false;

			nondeterministicBehavior.PriorityOverrides[0] = 17;
			M().ShouldBe(1);

			nondeterministicBehavior.PriorityOverrides[1] = 33;
			M().ShouldBe(2);

			//
			nondeterministicBehavior.ResetPriorityOverrides();
			Metadata.Faults[0].Fault.IsOccurring = true;
			Metadata.Faults[1].Fault.IsOccurring = false;
			Metadata.Faults[2].Fault.IsOccurring = true;

			nondeterministicBehavior.PriorityOverrides[0] = 17;
			M().ShouldBe(1);

			nondeterministicBehavior.PriorityOverrides[2] = 33;
			M().ShouldBe(3);

			//
			nondeterministicBehavior.ResetPriorityOverrides();
			Metadata.Faults[0].Fault.IsOccurring = false;
			Metadata.Faults[1].Fault.IsOccurring = true;
			Metadata.Faults[2].Fault.IsOccurring = true;

			nondeterministicBehavior.PriorityOverrides[1] = 17;
			M().ShouldBe(2);

			nondeterministicBehavior.PriorityOverrides[2] = 33;
			M().ShouldBe(3);

			// Three faults, deterministic
			nondeterministicBehavior.ResetPriorityOverrides();
			Metadata.Faults[0].Fault.IsOccurring = true;
			Metadata.Faults[1].Fault.IsOccurring = true;
			Metadata.Faults[2].Fault.IsOccurring = true;

			nondeterministicBehavior.PriorityOverrides[2] = 17;
			M().ShouldBe(3);

			nondeterministicBehavior.PriorityOverrides[1] = 77;
			M().ShouldBe(2);

			nondeterministicBehavior.PriorityOverrides[0] = 111;
			M().ShouldBe(1);
		}

		[Persistent]
		private class F1 : Fault
		{
			public int M()
			{
				return 1;
			}
		}

		[Persistent]
		private class F2 : Fault<X7>
		{
			public int M()
			{
				return 2;
			}
		}

		[Persistent]
		private class F3 : Fault<X7>
		{
			public int M()
			{
				return 3;
			}
		}
	}
}