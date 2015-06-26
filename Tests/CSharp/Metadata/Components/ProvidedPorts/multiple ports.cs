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

namespace Tests.Metadata.Components.ProvidedPorts
{
	using System;
	using SafetySharp.CompilerServices;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal class X3 : TestComponent
	{
		public int P { get; set; }

		[Provided]
		internal void M()
		{
		}

		protected int M(int i)
		{
			return i;
		}

		public bool M(ref int i)
		{
			return i == 1;
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(5);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(X3).GetMethod("get_P"));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].Name.ShouldBe("get_P");

			Metadata.ProvidedPorts[1].MethodInfo.ShouldBe(typeof(X3).GetMethod("set_P"));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[1].Name.ShouldBe("set_P");

			Metadata.ProvidedPorts[2].MethodInfo.ReturnType.ShouldBe(typeof(void));
			Metadata.ProvidedPorts[2].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[2].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[2].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[2].Name.ShouldBe("M");

			Metadata.ProvidedPorts[3].MethodInfo.ReturnType.ShouldBe(typeof(int));
			Metadata.ProvidedPorts[3].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[3].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[3].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[3].Name.ShouldBe("M1");

			Metadata.ProvidedPorts[4].MethodInfo.ReturnType.ShouldBe(typeof(bool));
			Metadata.ProvidedPorts[4].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[4].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[4].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[4].Name.ShouldBe("M2");
		}
	}
}