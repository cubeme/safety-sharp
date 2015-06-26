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

	internal class X9 : Component
	{
		private X9()
		{
			var x = ProvidedPorts.Xyz;
		}

		private void Xyz()
		{
		}
	}

	internal class X9b : Component
	{
		private X9b()
		{
			var x = ProvidedPorts.Xyz;
			var y = ProvidedPorts.Uvw;
			var z = ProvidedPorts.Abc;
		}

		private int Xyz { get { return 1; } }
		private int Uvq { set { } }
		private int Abc { get; set; }
	}

	internal class X10 : Component
	{
		private X10()
		{
			var x = (this).ProvidedPorts.Xyz;
		}

		private void Xyz()
		{
		}
	}

	internal class X11 : Component
	{
		private X11(X11 x)
		{
			var y = x.ProvidedPorts.Xyz;
		}

		private void Xyz()
		{
		}
	}

	internal class X12 : Component
	{
		private X12()
		{
			X12 x = null;
			var y = x.ProvidedPorts.Xyz;
		}

		private void Xyz()
		{
		}
	}

	internal class X13 : Component
	{
		private X13 x;

		private X13()
		{
			var y = x.ProvidedPorts.Xyz;
		}

		private void Xyz()
		{
		}
	}

	internal class X14 : Component
	{
		private X14()
		{
			var y = x.ProvidedPorts.Xyz;
		}

		private X14 x { get; set; }

		private void Xyz()
		{
		}
	}

	internal class X15 : Component
	{
		private X15()
		{
			var y = x().ProvidedPorts.Xyz;
		}

		private void Xyz()
		{
		}

		private X15 x()
		{
			return null;
		}
	}

	internal class Y16 : Component
	{
		public void Xyz()
		{
		}
	}

	internal class X16 : Component
	{
		private X16(Y16 y)
		{
			var z = y.ProvidedPorts.Xyz;
		}
	}

	internal interface I2 : IComponent
	{
		[Provided]
		void Xyz();
	}

	internal class X17 : Component
	{
		private X17(I2 y)
		{
			var z = y.ProvidedPorts.Xyz;
		}
	}

	internal interface I3 : IComponent
	{
		[Provided]
		void Xyz();
	}

	internal class X18 : Component
	{
		private X18(I3 y)
		{
			var z = (y.ProvidedPorts).Xyz;
		}
	}
}