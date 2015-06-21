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

namespace Tests.Metadata.Components.StepMethods
{
	using System;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal abstract class X5 : TestComponent
	{
		public override void Update()
		{
		}
	}

	internal class X6 : X5
	{
		public override void Update()
		{
		}

		protected override void Check()
		{
			Metadata.UpdateMethods.Length.ShouldBe(3);

			Metadata.UpdateMethods[0].MethodInfo.ShouldBe(typeof(Component).GetMethod("Update"));
			Metadata.UpdateMethods[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.UpdateMethods[0].BaseMethod.ShouldBe(null);
			Metadata.UpdateMethods[0].IsOverride.ShouldBe(false);
			Metadata.UpdateMethods[0].IsOverridden.ShouldBe(true);
			Metadata.UpdateMethods[0].OverridingMethod.ShouldBe(Metadata.UpdateMethods[1]);
			Metadata.UpdateMethods[0].VirtuallyInvokedMethod.ShouldBe(Metadata.UpdateMethods[2]);
			Metadata.UpdateMethods[0].Name.ShouldBe("Update");

			Metadata.UpdateMethods[1].MethodInfo.ShouldBe(typeof(X5).GetMethod("Update"));
			Metadata.UpdateMethods[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.UpdateMethods[1].BaseMethod.MethodInfo.ShouldBe(ComponentUpdatedMethod);
			Metadata.UpdateMethods[1].IsOverridden.ShouldBe(true);
			Metadata.UpdateMethods[1].OverridingMethod.ShouldBe(Metadata.UpdateMethods[2]);
			Metadata.UpdateMethods[1].IsOverride.ShouldBe(true);
			Metadata.UpdateMethods[1].VirtuallyInvokedMethod.ShouldBe(Metadata.UpdateMethods[2]);
			Metadata.UpdateMethods[1].Name.ShouldBe("Update");

			Metadata.UpdateMethods[2].MethodInfo.ShouldBe(typeof(X6).GetMethod("Update"));
			Metadata.UpdateMethods[2].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.UpdateMethods[2].BaseMethod.MethodInfo.ShouldBe(typeof(X5).GetMethod("Update"));
			Metadata.UpdateMethods[2].IsOverride.ShouldBe(true);
			Metadata.UpdateMethods[2].IsOverridden.ShouldBe(false);
			Metadata.UpdateMethods[2].OverridingMethod.ShouldBe(null);
			Metadata.UpdateMethods[2].VirtuallyInvokedMethod.ShouldBe(Metadata.UpdateMethods[2]);
			Metadata.UpdateMethods[2].Name.ShouldBe("Update");

			Metadata.StepMethod.ShouldBe(Metadata.UpdateMethods[2]);
		}
	}
}