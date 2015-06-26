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

	internal class X1 : Component
	{
		private X1()
		{
			var x = RequiredPorts.Xyz;
		}

		private extern void Xyz();
	}

	internal class X1b : Component
	{
		private X1b()
		{
			var x = RequiredPorts.Xyz;
			var y = RequiredPorts.Uvw;
			var z = RequiredPorts.Abc;
		}

		private extern int Xyz { get; }
		private extern int Uvw { set; }
		private extern int Abc { get; set; }
	}

	internal class X2 : Component
	{
		private X2()
		{
			var x = this.RequiredPorts.Xyz;
		}

		private extern void Xyz();
	}

	internal class X3 : Component
	{
		private X3(X3 x)
		{
			var y = x.RequiredPorts.Xyz;
		}

		private extern void Xyz();
	}

	internal class X4 : Component
	{
		private X4()
		{
			X4 x = null;
			var y = x.RequiredPorts.Xyz;
		}

		private extern void Xyz();
	}

	internal class X5 : Component
	{
		private X5 x;

		private X5()
		{
			var y = x.RequiredPorts.Xyz;
		}

		private extern void Xyz();
	}

	internal class X6 : Component
	{
		private X6()
		{
			var y = x.RequiredPorts.Xyz;
		}

		private X6 x { get; set; }
		private extern void Xyz();
	}

	internal class X7 : Component
	{
		private X7()
		{
			var y = x().RequiredPorts.Xyz;
		}

		private extern void Xyz();

		private X7 x()
		{
			return null;
		}
	}

	internal class Y8 : Component
	{
		public extern void Xyz();
	}

	internal class X8 : Component
	{
		private X8(Y8 y)
		{
			var z = y.RequiredPorts.Xyz;
		}
	}

	internal interface I1 : IComponent
	{
		[Required]
		void Xyz();
	}

	internal class X : Component
	{
		private X(I1 y)
		{
			var z = y.RequiredPorts.Xyz;
		}
	}
}