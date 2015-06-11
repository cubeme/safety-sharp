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

namespace Tests.Diagnostics.Bindings.Models.Invalid
{
	using System;
	using SafetySharp.Compiler.Analyzers;
	using SafetySharp.Modeling;

	internal class X2 : Component
	{
		public void M()
		{
		}

		public extern void N();
	}

	[Diagnostic(DiagnosticIdentifier.ExpectedPortDelegateCast, 47, 39, 3)]
	[Diagnostic(DiagnosticIdentifier.ExpectedPortDelegateCast, 48, 39, 6)]
	[Diagnostic(DiagnosticIdentifier.ExpectedPortDelegateCast, 49, 39, 9)]
	internal class M6 : Model
	{
		private X2 x;

		private M6()
		{
			Bind(x.RequiredPorts.N = (int)x.ProvidedPorts.M).Delayed();
			Bind(x.RequiredPorts.N = (object)x.ProvidedPorts.M).Delayed();
			Bind(x.RequiredPorts.N = (Component)((x.ProvidedPorts.M))).Delayed();
		}
	}
}