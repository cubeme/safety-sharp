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

namespace ProductionCell
{
	using SafetySharp.Modeling;

	public class Workpiece : Component
	{
		private State _state;

		public bool Drill()
		{
			return ChangeState(State.Unchanged, State.Drilled);
		}

		public bool Insert()
		{
			return ChangeState(State.Drilled, State.Inserted);
		}

		public bool Tighten()
		{
			return ChangeState(State.Inserted, State.Tightened);
		}

		private bool ChangeState(State requiredState, State newState)
		{
			if (_state != requiredState)
			{
				_state = State.Damaged;
				return false;
			}

			_state = newState;
			return true;
		}

		private enum State
		{
			Unchanged,
			Drilled,
			Inserted,
			Tightened,
			Damaged
		}
	}
}