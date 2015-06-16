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

	[Diagnostic(DiagnosticIdentifier.FaultEffectSignatureIncompatible, 53, 25, 9, "Tests.Diagnostics.FaultEffects.Invalid.X3.F.Void2Void(int)", "Tests.Diagnostics.FaultEffects.Invalid.X3.Void2Void()")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectSignatureIncompatible, 57, 24, 9, "Tests.Diagnostics.FaultEffects.Invalid.X3.F.Void2Void()", "Tests.Diagnostics.FaultEffects.Invalid.X3.Void2Void()")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectSignatureIncompatible, 62, 24, 7, "Tests.Diagnostics.FaultEffects.Invalid.X3.F.Int2Int(bool)", "Tests.Diagnostics.FaultEffects.Invalid.X3.Int2Int(int)")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectSignatureIncompatible, 67, 25, 7, "Tests.Diagnostics.FaultEffects.Invalid.X3.F.Int2Int(int)", "Tests.Diagnostics.FaultEffects.Invalid.X3.Int2Int(int)")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectSignatureIncompatible, 72, 25, 7, "Tests.Diagnostics.FaultEffects.Invalid.X3.F.Int2Int()", "Tests.Diagnostics.FaultEffects.Invalid.X3.Int2Int(int)")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectSignatureIncompatible, 76, 25, 10, "Tests.Diagnostics.FaultEffects.Invalid.X3.F.Overloaded()", "Tests.Diagnostics.FaultEffects.Invalid.X3.Overloaded(int)")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectSignatureIncompatible, 81, 25, 3, "Tests.Diagnostics.FaultEffects.Invalid.X3.F.Ref(out int)", "Tests.Diagnostics.FaultEffects.Invalid.X3.Ref(ref int)")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectSignatureIncompatible, 86, 25, 3, "Tests.Diagnostics.FaultEffects.Invalid.X3.F.Out(ref int)", "Tests.Diagnostics.FaultEffects.Invalid.X3.Out(out int)")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectSignatureIncompatible, 91, 25, 3, "Tests.Diagnostics.FaultEffects.Invalid.X3.F.Ref(int)", "Tests.Diagnostics.FaultEffects.Invalid.X3.Ref(ref int)")]
	[Diagnostic(DiagnosticIdentifier.FaultEffectSignatureIncompatible, 96, 25, 3, "Tests.Diagnostics.FaultEffects.Invalid.X3.F.Out(int)", "Tests.Diagnostics.FaultEffects.Invalid.X3.Out(out int)")]
	internal class X3 : Component
	{
		public extern void Void2Void();
		public extern int Int2Int(int a);
		private extern void Overloaded(int b);
		public extern void Overloaded();
		protected extern void Overloaded(bool d);
		internal extern void Ref(ref int q);
		public extern void Out(out int q);

		[Transient]
		private class F : Fault
		{
			public void Void2Void(int i)
			{
			}

			public int Void2Void()
			{
				return 0;
			}

			public int Int2Int(bool a)
			{
				return 1;
			}

			public bool Int2Int(int a)
			{
				return false;
			}

			public void Int2Int()
			{
			}

			public bool Overloaded()
			{
				return false;
			}

			public void Ref(out int q)
			{
				q = 0;
			}

			public void Out(ref int q)
			{
				q = 1;
			}

			public void Ref(int q)
			{
				q = 0;
			}

			public void Out(int q)
			{
				q = 1;
			}
		}
	}
}