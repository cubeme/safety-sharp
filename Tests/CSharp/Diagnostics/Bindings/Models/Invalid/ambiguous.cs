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

namespace Tests.Diagnostics.Bindings.Models.Invalid
{
	using System;
	using SafetySharp.Compiler.Analyzers;
	using SafetySharp.Modeling;

	[Diagnostic(DiagnosticIdentifier.AmbiguousBinding, 41, 18, 37,
		"'Tests.Diagnostics.Bindings.Models.Invalid.X3.N()', 'Tests.Diagnostics.Bindings.Models.Invalid.X3.N(int)'",
		"'Tests.Diagnostics.Bindings.Models.Invalid.X3.M()', 'Tests.Diagnostics.Bindings.Models.Invalid.X3.M(int)'")]
	[Diagnostic(DiagnosticIdentifier.AmbiguousBinding, 42, 18, 37,
		"'Tests.Diagnostics.Bindings.Models.Invalid.X3.N()', 'Tests.Diagnostics.Bindings.Models.Invalid.X3.N(int)'",
		"'Tests.Diagnostics.Bindings.Models.Invalid.X3.M()', 'Tests.Diagnostics.Bindings.Models.Invalid.X3.M(int)'")]
	internal class M7 : Model
	{
		private X3 y;

		private M7()
		{
			Bind(y.RequiredPorts.N = y.ProvidedPorts.M);
			Bind(y.RequiredPorts.N = y.ProvidedPorts.M).Delayed();
		}
	}

	internal class X3 : Component
	{
		public void M()
		{
		}

		public void M(int i)
		{
		}

		public extern void N();
		public extern void N(int i);
	}
}