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

namespace Tests.Metadata.Components.Bindings
{
	using System;
	using SafetySharp.CompilerServices;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal class X21 : Component
	{
		public extern void M();
	}

	internal class X22 : TestComponent
	{
		private readonly X21 _y = new X21();

		public X22()
		{
			Bind(((((_y).RequiredPorts).M) = (ProvidedPorts.M)));
		}

		private void M()
		{
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Bindings.Length.ShouldBe(1);

			Metadata.Bindings[0].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[0].RequiredPort.ShouldBe(_y.GetMetadata().RequiredPorts[0]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			_y.GetMetadata().RequiredPorts[0].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.ProvidedPorts[0].BoundRequiredPorts.ShouldBe(new[] { _y.GetMetadata().RequiredPorts[0] });
		}
	}
}