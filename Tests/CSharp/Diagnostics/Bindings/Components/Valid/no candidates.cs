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

namespace Tests.Diagnostics.Bindings.Components.Valid
{
	using System;
	using SafetySharp.Modeling;

	/* ============================================================================= */
	/* This is valid only because non-existing ports are handled by another analyzer */
	/* ============================================================================= */

	internal class X10 : Component
	{
		private X10()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M).Delayed();
		}

		private extern void N();
	}

	internal class X11 : Component
	{
		private X11()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		private void M()
		{
		}
	}

	internal class X12 : Component
	{
		private X12()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M).Delayed();
		}

		private void M()
		{
		}
	}

	internal class X13 : Component
	{
		private X13()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}
	}

	internal class X14 : Component
	{
		private X14()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M).Delayed();
		}
	}

	internal class X15 : Component
	{
		private X15()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		private extern void N();
	}
}