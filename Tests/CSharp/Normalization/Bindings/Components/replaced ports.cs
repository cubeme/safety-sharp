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

namespace Tests.Normalization.Bindings.Components
{
	using System;
	using SafetySharp.Modeling;

	internal class X12 : Component
	{
		public extern void N();

		public void M()
		{
		}
	}

	partial class In12 : X12
	{
		private In12()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
			Bind(((X12)this).RequiredPorts.N = ProvidedPorts.M);
			Bind(base.RequiredPorts.N = ProvidedPorts.M);
		}

		public new extern void N();

		public new void M()
		{
		}
	}

	partial class Out12 : X12
	{
		private Out12()
		{
			global::SafetySharp.CompilerServices.MetadataBuilders.GetBuilder(this).WithBinding(
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate0__), this, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.In12), "N", new System.Type[] { }, typeof(void))),
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate0__), this, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.In12), "M", new System.Type[] { }, typeof(void))));
			global::SafetySharp.CompilerServices.MetadataBuilders.GetBuilder(this).WithBinding(
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate1__), ((X12)this), SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.X12), "N", new System.Type[] { }, typeof(void))),
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate1__), this, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.In12), "M", new System.Type[] { }, typeof(void))));
			global::SafetySharp.CompilerServices.MetadataBuilders.GetBuilder(this).WithBinding(
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate2__), (global::Tests.Normalization.Bindings.Components.X12)(this), SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.X12), "N", new System.Type[] { }, typeof(void))),
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate2__), this, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.In12), "M", new System.Type[] { }, typeof(void))));
		}

		public new extern void N();

		public new void M()
		{
		}
	}

	partial class Out12
	{
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate void __BindingDelegate0__();

		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate void __BindingDelegate1__();

		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate void __BindingDelegate2__();
	}
}