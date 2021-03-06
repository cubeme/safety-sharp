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

	partial class In8 : Component
	{
		private In8(In8 x, In8 y)
		{
			Bind(x.RequiredPorts.N = y.ProvidedPorts.M);
		}

		private In8(In8 x)
		{
			Bind(x.RequiredPorts.Q = x.ProvidedPorts.P);
		}

		private void M()
		{
		}

		private int P()
		{
			return 1;
		}

		private extern void N();
		private extern int Q();
	}

	partial class Out8 : Component
	{
		private Out8(Out8 x, Out8 y)
		{
			global::SafetySharp.CompilerServices.MetadataBuilders.GetBuilder(this).WithBinding(
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate0__), x, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.In8), "N", new System.Type[] { }, typeof(void))),
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate0__), y, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.In8), "M", new System.Type[] { }, typeof(void))));
		}

		private Out8(Out8 x)
		{
			global::SafetySharp.CompilerServices.MetadataBuilders.GetBuilder(this).WithBinding(
					global::System.Delegate.CreateDelegate(typeof(__BindingDelegate1__), x, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.In8), "Q", new System.Type[] { }, typeof(System.Int32))),
					global::System.Delegate.CreateDelegate(typeof(__BindingDelegate1__), x, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.In8), "P", new System.Type[] { }, typeof(System.Int32))));
		}

		private void M()
		{
		}

		private int P()
		{
			return 1;
		}

		private extern void N();
		private extern int Q();
	}

	partial class Out8
	{
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate void __BindingDelegate0__();
	}

	partial class Out8
	{
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate int __BindingDelegate1__();
	}
}