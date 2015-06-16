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

namespace Tests.Metadata.Components.StepMethods
{
	using System;
	using System.Reflection;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal class X2 : TestComponent
	{
		public override void Update()
		{
		}

		protected override void Check()
		{
			Metadata.StepMethods.Length.ShouldBe(2);

			Metadata.StepMethods[0].MethodInfo.ShouldBe(typeof(Component).GetMethod("Update"));
			Metadata.StepMethods[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.StepMethods[0].BaseMethod.ShouldBe(null);
			Metadata.StepMethods[0].IsOverride.ShouldBe(false);
			Metadata.StepMethods[0].Name.ShouldBe("Update");

			Metadata.StepMethods[1].MethodInfo.ShouldBe(typeof(X2).GetMethod("Update"));
			Metadata.StepMethods[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.StepMethods[1].BaseMethod.MethodInfo.ShouldBe(ComponentUpdatedMethod);
			Metadata.StepMethods[1].IsOverride.ShouldBe(true);
			Metadata.StepMethods[1].Name.ShouldBe("Update");
			Metadata.StepMethods[1].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.StepMethods[1].HasImplementation.ShouldBe(true);
			Metadata.StepMethods[1].IntendedBehavior.ShouldBe(typeof(X2).GetMethod("__Behavior0__",
				BindingFlags.Instance | BindingFlags.NonPublic));
		}
	}
}