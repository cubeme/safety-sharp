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

	internal class X13 : Component
	{
		public extern void N1();
		public extern int N2(int i, out bool b);

		public virtual void M()
		{
		}

		public virtual int R(int i, out bool b)
		{
			b = false;
			return i;
		}
	}

	partial class In14 : X13
	{
		private In14()
		{
			Bind(RequiredPorts.N1 = base.ProvidedPorts.M);
			Bind(RequiredPorts.N2 = base.ProvidedPorts.R);
		}

		public override void M()
		{
		}

		public override int R(int i, out bool b)
		{
			b = true;
			return i;
		}
	}

	partial class Out14 : X13
	{
		private Out14()
		{
			global::SafetySharp.CompilerServices.MetadataBuilders.GetBuilder(this).WithBinding(
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate0__), this, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.X13), "N1", new System.Type[] { }, typeof(void))),
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate0__), this, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.In14), "__SynthesizedPort0__", new System.Type[] { }, typeof(void))));
			global::SafetySharp.CompilerServices.MetadataBuilders.GetBuilder(this).WithBinding(
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate1__), this, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.X13), "N2", new System.Type[] { typeof(System.Int32), (typeof(System.Boolean)).MakeByRefType() }, typeof(System.Int32))),
				global::System.Delegate.CreateDelegate(typeof(__BindingDelegate1__), this, SafetySharp.CompilerServices.ReflectionHelpers.GetMethod(typeof(global::Tests.Normalization.Bindings.Components.In14), "__SynthesizedPort1__", new System.Type[] { typeof(System.Int32), (typeof(System.Boolean)).MakeByRefType() }, typeof(System.Int32))));
		}

		public override void M()
		{
		}

		public override int R(int i, out bool b)
		{
			b = true;
			return i;
		}
	}

	partial class Out14
	{
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate void __BindingDelegate0__();
	}

	partial class Out14
	{
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate int __BindingDelegate1__(int i, out bool b);
	}

	partial class Out14
	{
		[global::SafetySharp.Modeling.ProvidedAttribute]
		[global::System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private void __SynthesizedPort0__()
		{
			base.M();
		}
	}

	partial class Out14
	{
		[global::SafetySharp.Modeling.ProvidedAttribute]
		[global::System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private System.Int32 __SynthesizedPort1__(System.Int32 i, out System.Boolean b)
		{
			return base.R(i, out b);
		}
	}
}