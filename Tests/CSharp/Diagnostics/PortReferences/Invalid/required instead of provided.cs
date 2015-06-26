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

namespace Tests.Diagnostics.PortReferences.Invalid
{
	using System;
	using SafetySharp.Compiler.Analyzers;
	using SafetySharp.Modeling;

	[Diagnostic(DiagnosticIdentifier.UnknownProvidedPort, 34, 35, 3, "Tests.Diagnostics.PortReferences.Invalid.X31", "Xyz")]
	internal class X31 : Component
	{
		private X31()
		{
			var x = ProvidedPorts.Xyz;
		}

		private extern void Xyz();
	}

	internal interface I9 : IComponent
	{
		[Required]
		void Xyz();
	}

	[Diagnostic(DiagnosticIdentifier.UnknownProvidedPort, 51, 37, 3, "Tests.Diagnostics.PortReferences.Invalid.I9", "Xyz")]
	internal class X32 : Component
	{
		private X32(I9 i)
		{
			var x = i.ProvidedPorts.Xyz;
		}
	}
}