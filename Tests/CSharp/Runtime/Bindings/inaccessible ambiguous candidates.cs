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

namespace Tests.Runtime.Bindings
{
	using System;
	using System.Linq;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Shouldly;

	internal class X39 : Component
	{
		private extern void N();
		public extern void N(int i);
	}

	internal class X40 : TestComponent
	{
		private readonly X39 _y = new X39();

		public X40()
		{
			Bind(_y.RequiredPorts.N = ProvidedPorts.M);
		}

		private void M()
		{
		}

		private void M(int i)
		{
		}

		protected override void Check()
		{
			Metadata.Bindings.Count().ShouldBe(1);

			Metadata.Bindings[0].Component.Component.ShouldBe(this);
			Metadata.Bindings[0].RequiredPort.ShouldBe(_y.GetComponentInfo().RequiredPorts[1]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[1]);
		}
	}
}