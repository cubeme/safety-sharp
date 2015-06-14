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

	internal interface I6 : IComponent
	{
		[Provided]
		void M();

		[Required]
		void N();
	}

	partial class In6 : Component
	{
		private I6 i;

		private In6()
		{
			Bind(X().i.RequiredPorts.N = X().i.ProvidedPorts.M);
		}

		private In6 X()
		{
			return null;
		}
	}

	partial class Out6 : Component
	{
		private I6 i;

		private Out6()
		{
			global::SafetySharp.CompilerServices.MetadataBuilders.GetBuilder(this).WithBinding(
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate0__), X().i, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.I6), "N", new System.Type[] { }, typeof(void))),
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate0__), X().i, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.I6), "M", new System.Type[] { }, typeof(void))));
		}

		private Out6 X()
		{
			return null;
		}
	}

	partial class Out6
	{
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate void __BindingDelegate0__();
	}
}