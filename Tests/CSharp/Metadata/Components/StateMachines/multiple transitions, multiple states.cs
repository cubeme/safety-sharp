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

	internal class C8 : TestComponent
	{
		public C8()
		{
			Transition(S.A, S.B);
			Transition(S.B, S.C);
			Transition(S.C, S.A);
			InitialState(S.A);
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.StateMachine.States.Count.ShouldBe(3);

			Metadata.StateMachine.States[0].StateMachine.ShouldBe(Metadata.StateMachine);
			Metadata.StateMachine.States[0].Identifier.ShouldBe(0);
			Metadata.StateMachine.States[0].Name.ShouldBe("A");
			Metadata.StateMachine.States[0].OutgoingTransitions.ShouldBe(new[] { Metadata.StateMachine.Transitions[0] });
			Metadata.StateMachine.States[0].IncomingTransitions.ShouldBe(new[] { Metadata.StateMachine.Transitions[2] });
			Metadata.StateMachine.States[0].SuccessorStates.ShouldBe(new[] { Metadata.StateMachine.States[1] });
			Metadata.StateMachine.States[0].PredecessorStates.ShouldBe(new[] { Metadata.StateMachine.States[2] });

			Metadata.StateMachine.States[1].StateMachine.ShouldBe(Metadata.StateMachine);
			Metadata.StateMachine.States[1].Identifier.ShouldBe(1);
			Metadata.StateMachine.States[1].Name.ShouldBe("B");
			Metadata.StateMachine.States[1].OutgoingTransitions.ShouldBe(new[] { Metadata.StateMachine.Transitions[1] });
			Metadata.StateMachine.States[1].IncomingTransitions.ShouldBe(new[] { Metadata.StateMachine.Transitions[0] });
			Metadata.StateMachine.States[1].SuccessorStates.ShouldBe(new[] { Metadata.StateMachine.States[2] });
			Metadata.StateMachine.States[1].PredecessorStates.ShouldBe(new[] { Metadata.StateMachine.States[0] });

			Metadata.StateMachine.States[2].StateMachine.ShouldBe(Metadata.StateMachine);
			Metadata.StateMachine.States[2].Identifier.ShouldBe(2);
			Metadata.StateMachine.States[2].Name.ShouldBe("C");
			Metadata.StateMachine.States[2].OutgoingTransitions.ShouldBe(new[] { Metadata.StateMachine.Transitions[2] });
			Metadata.StateMachine.States[2].IncomingTransitions.ShouldBe(new[] { Metadata.StateMachine.Transitions[1] });
			Metadata.StateMachine.States[2].SuccessorStates.ShouldBe(new[] { Metadata.StateMachine.States[0] });
			Metadata.StateMachine.States[2].PredecessorStates.ShouldBe(new[] { Metadata.StateMachine.States[1] });

			Metadata.StateMachine.Transitions.Count.ShouldBe(3);

			Metadata.StateMachine.Transitions[0].StateMachine.ShouldBe(Metadata.StateMachine);
			Metadata.StateMachine.Transitions[0].SourceState.ShouldBe(Metadata.StateMachine.States[0]);
			Metadata.StateMachine.Transitions[0].TargetState.ShouldBe(Metadata.StateMachine.States[1]);
			Metadata.StateMachine.Transitions[0].Guard.ShouldBe(null);
			Metadata.StateMachine.Transitions[0].Action.ShouldBe(null);

			Metadata.StateMachine.Transitions[1].StateMachine.ShouldBe(Metadata.StateMachine);
			Metadata.StateMachine.Transitions[1].SourceState.ShouldBe(Metadata.StateMachine.States[1]);
			Metadata.StateMachine.Transitions[1].TargetState.ShouldBe(Metadata.StateMachine.States[2]);
			Metadata.StateMachine.Transitions[1].Guard.ShouldBe(null);
			Metadata.StateMachine.Transitions[1].Action.ShouldBe(null);

			Metadata.StateMachine.Transitions[2].StateMachine.ShouldBe(Metadata.StateMachine);
			Metadata.StateMachine.Transitions[2].SourceState.ShouldBe(Metadata.StateMachine.States[2]);
			Metadata.StateMachine.Transitions[2].TargetState.ShouldBe(Metadata.StateMachine.States[0]);
			Metadata.StateMachine.Transitions[2].Guard.ShouldBe(null);
			Metadata.StateMachine.Transitions[2].Action.ShouldBe(null);
		}

		private enum S
		{
			A,
			B,
			C
		}
	}
}