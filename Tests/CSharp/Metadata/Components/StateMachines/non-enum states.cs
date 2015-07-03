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

namespace Tests.Metadata.Components.StateMachines
{
	using System;
	using SafetySharp.Modeling;
	using Shouldly;
	using Utilities;

	internal class T2 : TestObject
	{
		protected override void Check()
		{
			Tests.RaisesWith<ArgumentException>(() => new C1(), e => e.ParamName.ShouldBe("sourceState"));
			Tests.RaisesWith<ArgumentException>(() => new C2(), e => e.ParamName.ShouldBe("targetState"));
			Tests.RaisesWith<ArgumentException>(() => new C3(), e => e.ParamName.ShouldBe("initialStates"));
		}

		private class C1 : Component
		{
			public C1()
			{
				AddTransition(12, S.B);
			}

			private enum S
			{
				A,
				B
			}
		}

		private class C2 : Component
		{
			public C2()
			{
				AddTransition(S.B, 12);
			}

			private enum S
			{
				A,
				B
			}
		}

		private class C3 : Component
		{
			public C3()
			{
				AddTransition(S.B, S.A);
				AddInitialState(1);
			}

			private enum S
			{
				A,
				B
			}
		}
	}
}