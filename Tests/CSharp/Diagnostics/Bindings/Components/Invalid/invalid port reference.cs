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

	[Diagnostic(DiagnosticIdentifier.ExpectedPortReference, 37, 18, 1, "x")]
	[Diagnostic(DiagnosticIdentifier.ExpectedPortReference, 38, 18, 1, "x")]
	internal class X3 : Component
	{
		private dynamic x;

		private X3()
		{
			Bind(x = ProvidedPorts.X);
			Bind(x = ProvidedPorts.X).Delayed();
		}
	}

	[Diagnostic(DiagnosticIdentifier.ExpectedPortReference, 50, 36, 1, "x")]
	[Diagnostic(DiagnosticIdentifier.ExpectedPortReference, 51, 36, 1, "x")]
	internal class X4 : Component
	{
		private dynamic x;

		private X4()
		{
			Bind(RequiredPorts.X = x);
			Bind(RequiredPorts.X = x).Delayed();
		}
	}

	[Diagnostic(DiagnosticIdentifier.ExpectedPortReference, 64, 18, 3, "x.y")]
	[Diagnostic(DiagnosticIdentifier.ExpectedPortReference, 65, 18, 3, "x.y")]
	internal class X5 : Component
	{
		private X5 x;
		private dynamic y;

		private X5()
		{
			Bind(x.y = ProvidedPorts.X);
			Bind(x.y = ProvidedPorts.X).Delayed();
		}
	}

	[Diagnostic(DiagnosticIdentifier.ExpectedPortReference, 78, 36, 3, "x.y")]
	[Diagnostic(DiagnosticIdentifier.ExpectedPortReference, 79, 36, 3, "x.y")]
	internal class X6 : Component
	{
		private X6 x;
		private dynamic y;

		private X6()
		{
			Bind(RequiredPorts.X = x.y);
			Bind(RequiredPorts.X = x.y).Delayed();
		}
	}
}