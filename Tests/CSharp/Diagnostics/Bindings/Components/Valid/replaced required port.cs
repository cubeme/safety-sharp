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

	internal class X33 : Component
	{
		public extern int Q { get; }
		public extern void M();
	}

	internal class X34 : X33
	{
		private X34()
		{
			Bind(RequiredPorts.M = ProvidedPorts.N);
			Bind(((X33)this).RequiredPorts.M = ProvidedPorts.N);
			Bind(base.RequiredPorts.M = ProvidedPorts.N);

			Bind(RequiredPorts.Q = ProvidedPorts.P);
			Bind(((X33)this).RequiredPorts.Q = ProvidedPorts.P);
			Bind(base.RequiredPorts.Q = ProvidedPorts.P);
		}

		private int P { get; set; }
		public new extern int Q { get; }

		private void N()
		{
		}

		public new extern void M();
	}
}