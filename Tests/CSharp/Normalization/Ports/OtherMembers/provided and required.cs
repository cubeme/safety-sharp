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

namespace Tests.Normalization.Ports.Required
{
	using System;
	using SafetySharp.Runtime.Modeling;

	internal partial class In1 : Component
	{
		public extern void M1();
		public int M2(int x)
		{
			return x;
		}
	}

	internal partial class Out1 : Component
	{
		[SafetySharp.Runtime.Modeling.RequiredAttribute()]
		[System.Diagnostics.DebuggerHiddenAttribute()]
		[SafetySharp.Runtime.CompilerServices.BackingFieldAttribute("__portField0__")]
		public void M1() => this.__portField0__();

		private int __DefaultImplementation1__(int x)
		{
			return x;
		}
	}

	partial class Out1
	{
		[System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)]
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute()]
		private __PortDelegate0__ __portField0__;

		[System.Runtime.CompilerServices.CompilerGeneratedAttribute()]
		private delegate void __PortDelegate0__();

		[System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)]
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute()]
		private __PortDelegate1__ __portField1__;

		[System.Runtime.CompilerServices.CompilerGeneratedAttribute()]
		private delegate int __PortDelegate1__(int x);

		[SafetySharp.Runtime.Modeling.ProvidedAttribute()]
		[SafetySharp.Runtime.CompilerServices.PortBehaviorAttribute("__DefaultImplementation1__")]
		[System.Diagnostics.DebuggerHiddenAttribute()]
		[SafetySharp.Runtime.CompilerServices.BackingFieldAttribute("__portField1__")]
		public int M2(int x) => this.__portField1__(x);
	}
}