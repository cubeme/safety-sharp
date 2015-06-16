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

namespace Tests.Normalization.Methods.Required
{
	using System;
	using SafetySharp.Modeling;

	interface I1 : IComponent
	{
		[Provided]
		int M();
	}
	
	internal partial class In9 : Component, Tests.Normalization.Methods.Required.I1
	{
		int Tests.Normalization.Methods.Required.I1.M()
		{
			return 1;
		}
	}

	internal partial class Out9 : Component, Tests.Normalization.Methods.Required.I1
	{
		[SafetySharp.CompilerServices.SuppressTransformationAttribute]
		private int __Behavior0__()
		{
			return 1;
		}
	}

	partial class Out9
	{
		[System.Diagnostics.DebuggerBrowsableAttribute(global::System.Diagnostics.DebuggerBrowsableState.Never)]
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private __Delegate0__ __backingField0__;

		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate int __Delegate0__();

		[SafetySharp.Modeling.ProvidedAttribute]
		[SafetySharp.CompilerServices.MethodBehaviorAttribute("__Behavior0__")]
		[System.Diagnostics.DebuggerHiddenAttribute]
		[SafetySharp.CompilerServices.BackingFieldAttribute("__backingField0__")]
		int Tests.Normalization.Methods.Required.I1.M() => this.__backingField0__();
	}
}