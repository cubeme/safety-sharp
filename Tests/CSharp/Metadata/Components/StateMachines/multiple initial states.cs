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
	using SafetySharp.CompilerServices;
	using Shouldly;
	using Utilities;

	internal class C12 : TestComponent
	{
		public C12()
		{
			AddTransition(S.A, S.B);
			AddInitialState(S.A);
			AddInitialState(S.B);
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.StateMachine.InitialStates.ShouldBe(new[] { Metadata.StateMachine.States[0], Metadata.StateMachine.States[1] });
			Metadata.StateMachine.StateField.InitialValues.ShouldBe(new object[] { 0, 1 });
		}

		private enum S
		{
			A,
			B
		}
	}

	internal class C13 : TestComponent
	{
		public C13()
		{
			AddTransition(S.A, S.B);
			AddInitialStates(S.A, S.B);
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.StateMachine.InitialStates.ShouldBe(new[] { Metadata.StateMachine.States[0], Metadata.StateMachine.States[1] });
			Metadata.StateMachine.StateField.InitialValues.ShouldBe(new object[] { 0, 1 });
		}

		private enum S
		{
			A,
			B
		}
	}

	internal class C14 : TestComponent
	{
		public C14()
		{
			AddTransition(S.A, S.B);
			AddInitialStates(S.A, S.B, S.C);
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.StateMachine.InitialStates.ShouldBe(
				new[] { Metadata.StateMachine.States[0], Metadata.StateMachine.States[1], Metadata.StateMachine.States[2] });
			Metadata.StateMachine.StateField.InitialValues.ShouldBe(new object[] { 0, 1, 2 });
		}

		private enum S
		{
			A,
			B,
			C
		}
	}
}