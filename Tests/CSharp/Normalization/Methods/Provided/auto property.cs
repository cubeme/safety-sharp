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

	[CheckTrivia(TriviaType.DocCommentsAndDirectives)]
	internal partial class In1 : Component
	{
		public int M { get; set; }
	}

	[CheckTrivia(TriviaType.DocCommentsAndDirectives)]
	internal partial class Out1 : Component
	{
		[SafetySharp.CompilerServices.SuppressTransformationAttribute]
		private int __Behavior0__()
		{
			return __propertyBackingField0__;
		}

		[SafetySharp.CompilerServices.SuppressTransformationAttribute]
		private void __Behavior1__(int value)
		{
			__propertyBackingField0__ = value;
		}
#line 32
	}

	partial class Out1
	{
		[System.Diagnostics.DebuggerBrowsableAttribute(global::System.Diagnostics.DebuggerBrowsableState.Never)]
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private int __propertyBackingField0__;

		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate int __Delegate0__();

		[System.Diagnostics.DebuggerBrowsableAttribute(global::System.Diagnostics.DebuggerBrowsableState.Never)]
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private __Delegate0__ __backingField0__;

		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate void __Delegate1__(int value);

		[System.Diagnostics.DebuggerBrowsableAttribute(global::System.Diagnostics.DebuggerBrowsableState.Never)]
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private __Delegate1__ __backingField1__;

		[SafetySharp.Modeling.ProvidedAttribute]
		[System.Diagnostics.DebuggerHiddenAttribute]
		public int M
		{
			[SafetySharp.CompilerServices.IntendedBehaviorAttribute("__Behavior0__")]
			[SafetySharp.CompilerServices.BackingFieldAttribute("__backingField0__")]
			get { return __backingField0__(); } 

			[SafetySharp.CompilerServices.IntendedBehaviorAttribute("__Behavior1__")]
			[SafetySharp.CompilerServices.BackingFieldAttribute("__backingField1__")]
			set { __backingField1__(value);  }
		}
	}
}