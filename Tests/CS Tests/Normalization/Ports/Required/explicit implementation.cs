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
	using SafetySharp.Modeling;

	interface I1 : IComponent
	{
		[Required]
		void M();
	}
	
	internal partial class In9 : Component, Tests.Normalization.Ports.Required.I1
	{
		extern void Tests.Normalization.Ports.Required.I1.M();
	}

	internal partial class Out9 : Component, Tests.Normalization.Ports.Required.I1
	{
		[SafetySharp.Modeling.RequiredAttribute()]
		[SafetySharp.Modeling.BackingFieldAttribute("__portField0__")]
		void Tests.Normalization.Ports.Required.I1.M() => this.__portField0__();
	}

	partial class Out9
	{
		[System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)]
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute()]
		private __PortDelegate0__ __portField0__;

		[System.Runtime.CompilerServices.CompilerGeneratedAttribute()]
		private delegate void __PortDelegate0__();
	}
}