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

	[Diagnostic(DiagnosticIdentifier.FaultEffectBaseMember, 50, 25, 1, "Tests.Diagnostics.FaultEffects.Invalid.X9.F.M(bool)",
		"Tests.Diagnostics.FaultEffects.Invalid.X8.M(bool)")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectUnknownMethod, 54, 25, 1, "Tests.Diagnostics.FaultEffects.Invalid.X9.F.N()",
		"Tests.Diagnostics.FaultEffects.Invalid.X9", "N")]
	internal class X8 : Component
	{
		public void M(bool i)
		{
		}

		private void N()
		{
		}
	}

	internal class X9 : X8
	{
		[Transient]
		private class F : Fault
		{
			public void M(bool i)
			{
			}

			public void N()
			{
			}
		}
	}
}