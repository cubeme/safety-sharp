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
	using SafetySharp.Modeling;

	partial class In1 : Component
	{
		private In1 x;

		private In1()
		{
			Bind(x.RequiredPorts.N = x.ProvidedPorts.M);
		}

		private void M()
		{
		}

		private extern void N();
	}

	partial class Out1 : Component
	{
		private Out1 x;

		private Out1()
		{
			global::SafetySharp.CompilerServices.MetadataBuilders.GetBuilder(this).WithBinding(
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate0__), x, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.In1), "N", new System.Type[] { }, typeof(void))),
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate0__), x, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.In1), "M", new System.Type[] { }, typeof(void))));
		}

		private void M()
		{
		}

		private extern void N();
	}

	partial class Out1
	{
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate void __BindingDelegate0__();
	}
}