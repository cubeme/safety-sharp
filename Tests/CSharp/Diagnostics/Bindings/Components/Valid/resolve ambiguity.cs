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

namespace Tests.Diagnostics.Bindings.Components.Valid
{
	using System;
	using SafetySharp.Modeling;

	internal class Y1 : Component
	{
		protected extern void N();
		public extern void N(int i);
	}

	internal class X16 : Y1
	{
		private X16()
		{
			Bind(RequiredPorts.N = (Action)ProvidedPorts.M);
		}

		private void M()
		{
		}

		private void M(int i)
		{
		}
	}

	internal class Y2 : Component
	{
		protected extern void N();
		public extern void N(int i);
	}

	internal class X17 : Y2
	{
		private X17()
		{
			Bind(RequiredPorts.N = (Action<int>)ProvidedPorts.M);
		}

		private void M()
		{
		}

		private void M(int i)
		{
		}
	}

	internal delegate void D1(ref int i);

	internal class Y3 : Component
	{
		protected extern void N();
		public extern void N(ref int i);
	}

	internal class X18 : Y3
	{
		private X18()
		{
			Bind(RequiredPorts.N = (D1)ProvidedPorts.M);
		}

		private void M()
		{
		}

		private void M(ref int i)
		{
		}
	}
}