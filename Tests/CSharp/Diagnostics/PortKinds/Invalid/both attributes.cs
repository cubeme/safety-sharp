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

namespace Tests.Diagnostics.PortKinds.Invalid
{
	using System;
	using SafetySharp.Compiler.Analyzers;
	using SafetySharp.Runtime.Modeling;

	[Diagnostic(DiagnosticIdentifier.AmbiguousPortKind, 33, 22, 1, "Tests.Diagnostics.PortKinds.Invalid.A1.M()")]
	internal class A1 : Component
	{
		[Required, Provided]
		private void M()
		{
		}
	}

	[Diagnostic(DiagnosticIdentifier.AmbiguousPortKind, 42, 21, 1, "Tests.Diagnostics.PortKinds.Invalid.A2.M")]
	internal class A2 : Component
	{
		[Required, Provided]
		private int M { get; set; }
	}

	[Diagnostic(DiagnosticIdentifier.AmbiguousPortKind, 50, 22, 1, "Tests.Diagnostics.PortKinds.Invalid.A3.M()")]
	internal class A3 : Component
	{
		[Required]
		[Provided]
		private void M()
		{
		}
	}

	[Diagnostic(DiagnosticIdentifier.AmbiguousPortKind, 60, 21, 1, "Tests.Diagnostics.PortKinds.Invalid.A4.M")]
	internal class A4 : Component
	{
		[Required]
		[Provided]
		private int M { get; set; }
	}

	[Diagnostic(DiagnosticIdentifier.AmbiguousPortKind, 67, 14, 1, "Tests.Diagnostics.PortKinds.Invalid.B1.M()")]
	internal interface B1 : IComponent
	{
		[Required, Provided]
		void M();
	}

	[Diagnostic(DiagnosticIdentifier.AmbiguousPortKind, 74, 13, 1, "Tests.Diagnostics.PortKinds.Invalid.B2.M")]
	internal interface B2 : IComponent
	{
		[Required, Provided]
		int M { get; set; }
	}

	[Diagnostic(DiagnosticIdentifier.AmbiguousPortKind, 82, 14, 1, "Tests.Diagnostics.PortKinds.Invalid.B3.M()")]
	internal interface B3 : IComponent
	{
		[Required]
		[Provided]
		void M();
	}

	[Diagnostic(DiagnosticIdentifier.AmbiguousPortKind, 90, 13, 1, "Tests.Diagnostics.PortKinds.Invalid.B4.M")]
	internal interface B4 : IComponent
	{
		[Required]
		[Provided]
		int M { get; set; }
	}
}