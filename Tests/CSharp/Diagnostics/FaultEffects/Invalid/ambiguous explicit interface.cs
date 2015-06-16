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

namespace Tests.Diagnostics.FaultEffects.Invalid
{
	using System;
	using SafetySharp.Compiler.Analyzers;
	using SafetySharp.Modeling;
	using SafetySharp.Modeling.Faults;

	internal interface I13
	{
		[Required]
		int R1 { get; set; }

		[Provided]
		int R2 { get; set; }

		[Required]
		void M1();

		[Provided]
		void M2();
	}

	[Diagnostic(DiagnosticIdentifier.FaultEffectAmbiguousMember, 78, 24, 2, "Tests.Diagnostics.FaultEffects.Invalid.X13.F.R1",
		"'Tests.Diagnostics.FaultEffects.Invalid.X13.R1', " +
		"'Tests.Diagnostics.FaultEffects.Invalid.X13.Tests.Diagnostics.FaultEffects.Invalid.I13.R1'")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectAmbiguousMember, 79, 24, 2, "Tests.Diagnostics.FaultEffects.Invalid.X13.F.R2",
		"'Tests.Diagnostics.FaultEffects.Invalid.X13.R2', " +
		"'Tests.Diagnostics.FaultEffects.Invalid.X13.Tests.Diagnostics.FaultEffects.Invalid.I13.R2'")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectAmbiguousMember, 80, 32, 2, "Tests.Diagnostics.FaultEffects.Invalid.X13.F.M1()",
		"'Tests.Diagnostics.FaultEffects.Invalid.X13.Tests.Diagnostics.FaultEffects.Invalid.I13.M1()', " +
		"'Tests.Diagnostics.FaultEffects.Invalid.X13.M1()'")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectAmbiguousMember, 82, 25, 2, "Tests.Diagnostics.FaultEffects.Invalid.X13.F.M2()",
		"'Tests.Diagnostics.FaultEffects.Invalid.X13.Tests.Diagnostics.FaultEffects.Invalid.I13.M2()', " +
		"'Tests.Diagnostics.FaultEffects.Invalid.X13.M2()'")]
	internal class X13 : Component, I13
	{
		public extern int R1 { get; set; }
		public int R2 { get; set; }
		extern int I13.R1 { get; set; }
		int I13.R2 { get; set; }
		extern void I13.M1();

		void I13.M2()
		{
		}

		public extern void M1();

		public void M2()
		{
		}

		[Transient]
		private class F : Fault
		{
			public int R1 { get; set; }
			public int R2 { get; set; }
			public extern void M1();

			public void M2()
			{
			}
		}
	}
}