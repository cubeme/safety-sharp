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

namespace Tests.Diagnostics.PortReferences.Valid
{
	using System;
	using SafetySharp.Modeling;

	internal class Y1 : Component
	{
		protected extern int P { get; }
		protected extern void M();
	}

	internal class X20 : Y1
	{
		private X20()
		{
			var y = RequiredPorts.M;
			var z = RequiredPorts.P;
		}
	}

	internal class Y2 : Component
	{
		protected int P
		{
			get { return 1; }
		}

		protected void M()
		{
		}
	}

	internal class X21 : Y2
	{
		private X21()
		{
			var y = ProvidedPorts.M;
			var z = ProvidedPorts.P;
		}
	}

	internal interface J1 : I4
	{
	}

	internal interface I4 : IComponent
	{
		[Required]
		int P { get; }

		[Required]
		void M();
	}

	internal class X22 : Component
	{
		private X22(J1 j)
		{
			var y = j.RequiredPorts.M;
			var z = j.RequiredPorts.P;
		}
	}

	internal interface J2 : I5
	{
	}

	internal interface I5 : IComponent
	{
		[Provided]
		int P { get; }

		[Provided]
		void M();
	}

	internal class X23 : Component
	{
		private X23(J2 j)
		{
			var y = j.ProvidedPorts.M;
			var z = j.ProvidedPorts.P;
		}
	}
}