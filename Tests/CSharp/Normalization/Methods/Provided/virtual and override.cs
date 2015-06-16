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

namespace Tests.Normalization.Methods.Provided
{
	using System;
	using SafetySharp.Modeling;

	internal partial class In1 : Component
	{
		public virtual int M(int x)
		{
			return x;
		}
	}

	internal partial class In2 : In1
	{
		public override int M(int x)
		{
			return base.M(x);
		}
	}

	internal partial class In3 : In2
	{
		public sealed override int M(int x)
		{
			return 1;
		}
	}

	internal partial class Out1 : Component
	{
		[SafetySharp.CompilerServices.SuppressTransformationAttribute]
		private int __Behavior0__(int x)
		{
			return x;
		}
	}

	internal partial class Out2 : Out1
	{
		[SafetySharp.CompilerServices.SuppressTransformationAttribute]
		private int __Behavior1__(int x)
		{
			return base.M(x);
		}
	}

	internal partial class Out3 : Out2
	{
		[SafetySharp.CompilerServices.SuppressTransformationAttribute]
		private int __Behavior2__(int x)
		{
			return 1;
		}
	}

	partial class Out1
	{
		[System.Diagnostics.DebuggerBrowsableAttribute(global::System.Diagnostics.DebuggerBrowsableState.Never)]
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private __Delegate0__ __backingField0__;

		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate int __Delegate0__(int x);

		[SafetySharp.Modeling.ProvidedAttribute]
		[SafetySharp.CompilerServices.MethodBehaviorAttribute("__Behavior0__")]
		[System.Diagnostics.DebuggerHiddenAttribute]
		[SafetySharp.CompilerServices.BackingFieldAttribute("__backingField0__")]
		public virtual int M(int x) => this.__backingField0__(x);
	}

	partial class Out2
	{
		[System.Diagnostics.DebuggerBrowsableAttribute(global::System.Diagnostics.DebuggerBrowsableState.Never)]
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private __Delegate1__ __backingField1__;

		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate int __Delegate1__(int x);

		[SafetySharp.Modeling.ProvidedAttribute]
		[SafetySharp.CompilerServices.MethodBehaviorAttribute("__Behavior1__")]
		[System.Diagnostics.DebuggerHiddenAttribute]
		[SafetySharp.CompilerServices.BackingFieldAttribute("__backingField1__")]
		public override int M(int x) => this.__backingField1__(x);
	}

	partial class Out3
	{
		[System.Diagnostics.DebuggerBrowsableAttribute(global::System.Diagnostics.DebuggerBrowsableState.Never)]
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private __Delegate2__ __backingField2__;

		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate int __Delegate2__(int x);

		[SafetySharp.Modeling.ProvidedAttribute]
		[SafetySharp.CompilerServices.MethodBehaviorAttribute("__Behavior2__")]
		[System.Diagnostics.DebuggerHiddenAttribute]
		[SafetySharp.CompilerServices.BackingFieldAttribute("__backingField2__")]
		public sealed override int M(int x) => this.__backingField2__(x);
	}
}