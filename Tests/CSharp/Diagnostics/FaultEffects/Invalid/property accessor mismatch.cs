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

namespace Tests.Diagnostics.FaultEffects.Invalid
{
	using System;
	using SafetySharp.Compiler.Analyzers;
	using SafetySharp.Modeling;
	using SafetySharp.Modeling.Faults;

	[Diagnostic(DiagnosticIdentifier.FaultEffectUnknownProperty, 49, 24, 2, "Tests.Diagnostics.FaultEffects.Invalid.X12.F.P1",
		"Tests.Diagnostics.FaultEffects.Invalid.X12", "P1", "int", "setter")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectUnknownProperty, 50, 24, 2, "Tests.Diagnostics.FaultEffects.Invalid.X12.F.P2",
		"Tests.Diagnostics.FaultEffects.Invalid.X12", "P2", "int", "getter")]
	internal class X12 : Component
	{
		public int P1
		{
			get { return 1; }
		}

		public int P2
		{
			set { }
		}

		[Transient]
		private class F : Fault
		{
			public int P1 { get; set; }
			public int P2 { get; set; }
		}
	}
}