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

namespace Tests.Normalization.Ports.Provided
{
	using System;
	using SafetySharp.Modeling;

	internal partial class In1 : Component
	{
		public void M1()
		{
			var i = 1 + 2;
		}

		partial class In2 : Component
		{
			internal void M2()
			{
				var i = 1 + 2;
			}
		}

		protected internal void M3()
		{
			var i = 1 + 2;
		}
	}

	internal partial class Out1 : Component
	{
		private void __DefaultImplementation0__()
		{
			var i = 1 + 2;
		}

		partial class Out2 : Component
		{
			private void __DefaultImplementation0__()
			{
				var i = 1 + 2;
			}
		}

		private void __DefaultImplementation1__()
		{
			var i = 1 + 2;
		}
	}

	partial class Out1
	{
		[System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)]
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute()]
		private __PortDelegate0__ __portField0__;

		[System.Runtime.CompilerServices.CompilerGeneratedAttribute()]
		private delegate void __PortDelegate0__();

		[SafetySharp.Modeling.ProvidedAttribute()]
		[SafetySharp.CompilerServices.PortBehaviorAttribute("__DefaultImplementation0__")]
		[System.Diagnostics.DebuggerHiddenAttribute()]
		[SafetySharp.CompilerServices.BackingFieldAttribute("__portField0__")]
		public void M1() => this.__portField0__();

		[System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)]
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute()]
		private __PortDelegate1__ __portField1__;

		[System.Runtime.CompilerServices.CompilerGeneratedAttribute()]
		private delegate void __PortDelegate1__();

		[SafetySharp.Modeling.ProvidedAttribute()]
		[SafetySharp.CompilerServices.PortBehaviorAttribute("__DefaultImplementation1__")]
		[System.Diagnostics.DebuggerHiddenAttribute()]
		[SafetySharp.CompilerServices.BackingFieldAttribute("__portField1__")]
		protected internal void M3() => this.__portField1__();
	}

	partial class Out1
	{
		partial class Out2
		{
			[System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)]
			[System.Runtime.CompilerServices.CompilerGeneratedAttribute()]
			private __PortDelegate0__ __portField0__;

			[System.Runtime.CompilerServices.CompilerGeneratedAttribute()]
			private delegate void __PortDelegate0__();

			[SafetySharp.Modeling.ProvidedAttribute()]
			[SafetySharp.CompilerServices.PortBehaviorAttribute("__DefaultImplementation0__")]
		[System.Diagnostics.DebuggerHiddenAttribute()]
			[SafetySharp.CompilerServices.BackingFieldAttribute("__portField0__")]
			internal void M2() => this.__portField0__();
		}
	}
}