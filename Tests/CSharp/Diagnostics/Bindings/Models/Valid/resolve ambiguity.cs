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

namespace Tests.Diagnostics.Bindings.Models.Valid
{
	using System;
	using SafetySharp.Modeling;

	internal class X2 : Component
	{
		public extern void N();
		public extern void N(int i);
	}

	internal class X3 : X2
	{
		public void M()
		{
		}

		public void M(int i)
		{
		}
	}

	internal class M2 : Model
	{
		private X2 x;

		private M2()
		{
			Bind(x.RequiredPorts.N = (Action)x.ProvidedPorts.M);
		}
	}

	internal class X4 : Component
	{
		public extern void N();
		public extern void N(int i);
	}

	internal class X5 : X4
	{
		public void M()
		{
		}

		public void M(int i)
		{
		}
	}

	internal class M3 : Model
	{
		private X5 x;

		private M3()
		{
			Bind(x.RequiredPorts.N = (Action<int>)x.ProvidedPorts.M);
		}
	}

	internal delegate void D1(ref int i);

	internal class X6 : Component
	{
		public extern void N();
		public extern void N(ref int i);
	}

	internal class X7 : X6
	{
		public void M()
		{
		}

		public void M(ref int i)
		{
		}
	}

	internal class M4 : Model
	{
		private X7 x;

		private M4()
		{
			Bind(x.RequiredPorts.N = (D1)x.ProvidedPorts.M);
		}
	}

	

	internal class P7 : Component
	{
		public int P { get; set; }
		public extern int Q { get; set; }
	}

	internal class P4 : Model
	{
		private P7 x;

		private P4()
		{
			Bind(x.RequiredPorts.Q = (Action<int>)x.ProvidedPorts.P);
			Bind(x.RequiredPorts.Q = (Func<int>)x.ProvidedPorts.P);
		}
	}
}