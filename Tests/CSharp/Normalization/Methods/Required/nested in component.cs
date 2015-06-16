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

namespace Tests.Normalization.Methods.Required
{
	using System;
	using SafetySharp.Modeling;

	internal partial class In1 : Component
	{
		public extern void M1();

		partial class In2 : Component
		{
			internal extern void M2();
		}

		protected internal extern void M3();
	}

	internal partial class Out1 : Component
	{
		[SafetySharp.Modeling.RequiredAttribute]
		[System.Diagnostics.DebuggerHiddenAttribute]
		[SafetySharp.CompilerServices.BackingFieldAttribute("__backingField0__")]
		public void M1() => this.__backingField0__();

		partial class Out2 : Component
		{
			[SafetySharp.Modeling.RequiredAttribute]
			[System.Diagnostics.DebuggerHiddenAttribute]
			[SafetySharp.CompilerServices.BackingFieldAttribute("__backingField1__")]
			internal void M2() => this.__backingField1__();
		}

		[SafetySharp.Modeling.RequiredAttribute]
		[System.Diagnostics.DebuggerHiddenAttribute]
		[SafetySharp.CompilerServices.BackingFieldAttribute("__backingField2__")]
		protected internal void M3() => this.__backingField2__();
	}

	partial class Out1
	{
		[System.Diagnostics.DebuggerBrowsableAttribute(global::System.Diagnostics.DebuggerBrowsableState.Never)]
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private __Delegate0__ __backingField0__;

		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate void __Delegate0__();
		
	}
	
	partial class Out1
	{
		[System.Diagnostics.DebuggerBrowsableAttribute(global::System.Diagnostics.DebuggerBrowsableState.Never)]
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private __Delegate2__ __backingField2__;

		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate void __Delegate2__();
	}

	partial class Out1
	{
		partial class Out2
		{
			[System.Diagnostics.DebuggerBrowsableAttribute(global::System.Diagnostics.DebuggerBrowsableState.Never)]
			[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
			private __Delegate1__ __backingField1__;

			[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
			private delegate void __Delegate1__();
		}
	}
}