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

namespace Tests.Normalization.Bindings.Components
{
	using System;
	using SafetySharp.Runtime.Modeling;

	partial class In2 : Component
	{
		private In2(In2 x, In2 y)
		{
			Bind(x.RequiredPorts.N = y.ProvidedPorts.M).Delayed();
		}

		private void M(ref int i)
		{
		}

		private extern void N(ref int i);
	}

	partial class Out2 : Component
	{
		private Out2(Out2 x, Out2 y)
		{
			Bind(new SafetySharp.Runtime.Modeling.PortBinding(
				SafetySharp.Runtime.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.N)),
				SafetySharp.Runtime.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(y.M))))
				.Delayed();
		}

		private void M(ref int i)
		{
		}

		private extern void N(ref int i);
	}

	partial class Out2
	{
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute()]
		private delegate void __BindingDelegate0__(ref int i);
	}
}