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

	[Diagnostic(DiagnosticIdentifier.FaultEffectUnknownProperty, 55, 25, 7, "Tests.Diagnostics.FaultEffects.Invalid.X5.F.GetProp",
		"Tests.Diagnostics.FaultEffects.Invalid.X5", "GetProp", "bool", "getter")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectUnknownProperty, 60, 25, 7, "Tests.Diagnostics.FaultEffects.Invalid.X5.F.SetProp",
		"Tests.Diagnostics.FaultEffects.Invalid.X5", "SetProp", "bool", "setter")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectUnknownProperty, 65, 25, 4, "Tests.Diagnostics.FaultEffects.Invalid.X5.F.Prop",
		"Tests.Diagnostics.FaultEffects.Invalid.X5", "Prop", "bool", "getter")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectUnknownProperty, 65, 25, 4, "Tests.Diagnostics.FaultEffects.Invalid.X5.F.Prop",
		"Tests.Diagnostics.FaultEffects.Invalid.X5", "Prop", "bool", "setter")]
	internal class X5 : Component
	{
		public int GetProp
		{
			get { return 1; }
		}

		private int SetProp
		{
			set { }
		}

		public int Prop { get; set; }

		[Transient]
		private class F : Fault
		{
			public bool GetProp
			{
				get { return false; }
			}

			public bool SetProp
			{
				set { }
			}

			public bool Prop { get; set; }
		}
	}
}