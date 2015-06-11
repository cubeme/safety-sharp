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

namespace Tests.Diagnostics.Bindings.Components.Invalid
{
	using System;
	using SafetySharp.Compiler.Analyzers;
	using SafetySharp.Modeling;

	[Diagnostic(DiagnosticIdentifier.AmbiguousBinding, 39, 18, 33,
		"'Tests.Diagnostics.Bindings.Components.Invalid.X12.N()', 'Tests.Diagnostics.Bindings.Components.Invalid.X12.N(int)'",
		"'Tests.Diagnostics.Bindings.Components.Invalid.X12.M()', 'Tests.Diagnostics.Bindings.Components.Invalid.X12.M(int)'")]
	[Diagnostic(DiagnosticIdentifier.AmbiguousBinding, 40, 18, 33,
		"'Tests.Diagnostics.Bindings.Components.Invalid.X12.N()', 'Tests.Diagnostics.Bindings.Components.Invalid.X12.N(int)'",
		"'Tests.Diagnostics.Bindings.Components.Invalid.X12.M()', 'Tests.Diagnostics.Bindings.Components.Invalid.X12.M(int)'")]
	internal class X12 : Component
	{
		private X12()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M).Delayed();
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		private void M()
		{
		}

		private void M(int i)
		{
		}

		private extern void N();
		private extern void N(int i);
	}

	[Diagnostic(DiagnosticIdentifier.AmbiguousBinding, 65, 18, 33,
		"'Tests.Diagnostics.Bindings.Components.Invalid.X13.N(int)', 'Tests.Diagnostics.Bindings.Components.Invalid.X13.N(ref int)'",
		"'Tests.Diagnostics.Bindings.Components.Invalid.X13.M(int)', 'Tests.Diagnostics.Bindings.Components.Invalid.X13.M(ref int)'")]
	[Diagnostic(DiagnosticIdentifier.AmbiguousBinding, 66, 18, 33,
		"'Tests.Diagnostics.Bindings.Components.Invalid.X13.N(int)', 'Tests.Diagnostics.Bindings.Components.Invalid.X13.N(ref int)'",
		"'Tests.Diagnostics.Bindings.Components.Invalid.X13.M(int)', 'Tests.Diagnostics.Bindings.Components.Invalid.X13.M(ref int)'")]
	internal class X13 : Component
	{
		private X13()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M).Delayed();
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		private void M(int i)
		{
		}

		private void M(ref int i)
		{
		}

		private extern void N(int i);
		private extern void N(ref int i);
	}

	[Diagnostic(DiagnosticIdentifier.AmbiguousBinding, 91, 18, 33,
		"'Tests.Diagnostics.Bindings.Components.Invalid.X14.N(int)', 'Tests.Diagnostics.Bindings.Components.Invalid.X14.N(ref int)'",
		"'Tests.Diagnostics.Bindings.Components.Invalid.X14.M(int)', 'Tests.Diagnostics.Bindings.Components.Invalid.X14.M(ref int)'")]
	[Diagnostic(DiagnosticIdentifier.AmbiguousBinding, 92, 18, 33,
		"'Tests.Diagnostics.Bindings.Components.Invalid.X14.N(int)', 'Tests.Diagnostics.Bindings.Components.Invalid.X14.N(ref int)'",
		"'Tests.Diagnostics.Bindings.Components.Invalid.X14.M(int)', 'Tests.Diagnostics.Bindings.Components.Invalid.X14.M(ref int)'")]
	internal class X14 : Component
	{
		private X14()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
			Bind(RequiredPorts.N = ProvidedPorts.M).Delayed();
		}

		private void M(int i)
		{
		}

		private void M(ref int i)
		{
		}

		private void M(out bool b)
		{
			b = false;
		}

		private extern void N(int i);
		private extern void N(ref int i);
	}

	[Diagnostic(DiagnosticIdentifier.AmbiguousBinding, 126, 18, 33,
		"'Tests.Diagnostics.Bindings.Components.Invalid.X15.N(out bool)', 'Tests.Diagnostics.Bindings.Components.Invalid.X15.N(int)', " +
		"'Tests.Diagnostics.Bindings.Components.Invalid.X15.N(ref int)'",
		"'Tests.Diagnostics.Bindings.Components.Invalid.X15.M(out bool)', 'Tests.Diagnostics.Bindings.Components.Invalid.X15.M(int)', " +
		"'Tests.Diagnostics.Bindings.Components.Invalid.X15.M(ref int)'")]
	[Diagnostic(DiagnosticIdentifier.AmbiguousBinding, 127, 18, 33,
		"'Tests.Diagnostics.Bindings.Components.Invalid.X15.N(out bool)', 'Tests.Diagnostics.Bindings.Components.Invalid.X15.N(int)', " +
		"'Tests.Diagnostics.Bindings.Components.Invalid.X15.N(ref int)'",
		"'Tests.Diagnostics.Bindings.Components.Invalid.X15.M(out bool)', 'Tests.Diagnostics.Bindings.Components.Invalid.X15.M(int)', " +
		"'Tests.Diagnostics.Bindings.Components.Invalid.X15.M(ref int)'")]
	internal class X15 : Component
	{
		private X15()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
			Bind(RequiredPorts.N = ProvidedPorts.M).Delayed();
		}

		private void M(int i)
		{
		}

		private void M(ref int i)
		{
		}

		private void M(out bool b)
		{
			b = false;
		}

		private extern void N(out bool b);
		private extern void N(int i);
		private extern void N(ref int i);
	}
}