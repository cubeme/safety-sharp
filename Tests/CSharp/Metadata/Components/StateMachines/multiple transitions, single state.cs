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

	internal class C5 : TestComponent
	{
		public C5()
		{
			AddTransition(S.A, S.A, guard: () => true);
			AddTransition(S.A, S.A, action: () => { });
			AddTransition(S.A, S.A, () => true, () => { });
			AddTransition(S.A, S.A, Guard, Action);
			AddInitialState(S.A);
		}

		private bool Guard()
		{
			return false;
		}

		private void Action()
		{
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.StateMachine.States.Count.ShouldBe(1);

			var transitions = new[]
			{
				Metadata.StateMachine.Transitions[0],
				Metadata.StateMachine.Transitions[1],
				Metadata.StateMachine.Transitions[2],
				Metadata.StateMachine.Transitions[3]
			};

			Metadata.StateMachine.States[0].StateMachine.ShouldBe(Metadata.StateMachine);
			Metadata.StateMachine.States[0].Identifier.ShouldBe(0);
			Metadata.StateMachine.States[0].Name.ShouldBe("A");
			Metadata.StateMachine.States[0].OutgoingTransitions.ShouldBe(transitions);
			Metadata.StateMachine.States[0].IncomingTransitions.ShouldBe(transitions);

			Metadata.StateMachine.Transitions.Count.ShouldBe(4);

			Metadata.StateMachine.Transitions[0].StateMachine.ShouldBe(Metadata.StateMachine);
			Metadata.StateMachine.Transitions[0].SourceState.ShouldBe(Metadata.StateMachine.States[0]);
			Metadata.StateMachine.Transitions[0].TargetState.ShouldBe(Metadata.StateMachine.States[0]);
			Metadata.StateMachine.Transitions[0].Guard.ShouldNotBe(null);
			Metadata.StateMachine.Transitions[0].Guard.Transition.ShouldBe(Metadata.StateMachine.Transitions[0]);
			Metadata.StateMachine.Transitions[0].Action.ShouldBe(null);

			Metadata.StateMachine.Transitions[1].StateMachine.ShouldBe(Metadata.StateMachine);
			Metadata.StateMachine.Transitions[1].SourceState.ShouldBe(Metadata.StateMachine.States[0]);
			Metadata.StateMachine.Transitions[1].TargetState.ShouldBe(Metadata.StateMachine.States[0]);
			Metadata.StateMachine.Transitions[1].Guard.ShouldBe(null);
			Metadata.StateMachine.Transitions[1].Action.ShouldNotBe(null);
			Metadata.StateMachine.Transitions[1].Action.Transition.ShouldBe(Metadata.StateMachine.Transitions[1]);

			Metadata.StateMachine.Transitions[2].StateMachine.ShouldBe(Metadata.StateMachine);
			Metadata.StateMachine.Transitions[2].SourceState.ShouldBe(Metadata.StateMachine.States[0]);
			Metadata.StateMachine.Transitions[2].TargetState.ShouldBe(Metadata.StateMachine.States[0]);
			Metadata.StateMachine.Transitions[2].Guard.ShouldNotBe(null);
			Metadata.StateMachine.Transitions[2].Action.ShouldNotBe(null);
			Metadata.StateMachine.Transitions[2].Guard.Transition.ShouldBe(Metadata.StateMachine.Transitions[2]);
			Metadata.StateMachine.Transitions[2].Action.Transition.ShouldBe(Metadata.StateMachine.Transitions[2]);

			Metadata.StateMachine.Transitions[3].StateMachine.ShouldBe(Metadata.StateMachine);
			Metadata.StateMachine.Transitions[3].SourceState.ShouldBe(Metadata.StateMachine.States[0]);
			Metadata.StateMachine.Transitions[3].TargetState.ShouldBe(Metadata.StateMachine.States[0]);
			Metadata.StateMachine.Transitions[3].Guard.ShouldNotBe(null);
			Metadata.StateMachine.Transitions[3].Action.ShouldNotBe(null);
			Metadata.StateMachine.Transitions[3].Guard.Transition.ShouldBe(Metadata.StateMachine.Transitions[3]);
			Metadata.StateMachine.Transitions[3].Action.Transition.ShouldBe(Metadata.StateMachine.Transitions[3]);
		}

		private enum S
		{
			A
		}
	}
}