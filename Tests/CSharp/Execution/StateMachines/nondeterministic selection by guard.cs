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

namespace Tests.Execution.StateMachines
{
	using System;
	using SafetySharp.CompilerServices;
	using Shouldly;
	using Utilities;

	internal class C10 : TestComponent
	{
		private int _f;

		public C10()
		{
			Transition(S.A, S.B, guard: () => _f > 0, action: () => _f = 17);
			Transition(S.A, S.B, guard: () => _f < 0, action: () => --_f);
			Transition(S.B, S.A);
			InitialState(S.A);
		}

		[SuppressTransformation]
		protected override void Check()
		{
			State.As<S>().ShouldBe(S.A);
			(State == S.A).ShouldBe(true);
			(State == S.B).ShouldBe(false);

			_f = 0;
			ExecuteUpdate();

			(State == S.A).ShouldBe(true);

			_f = -17;
			ExecuteUpdate();

			(State == S.B).ShouldBe(true);
			_f.ShouldBe(-18);

			_f = 33;
			ExecuteUpdate();
			ExecuteUpdate();

			(State == S.B).ShouldBe(true);
			_f.ShouldBe(17);
		}

		private enum S
		{
			A,
			B,
			C
		}
	}
}