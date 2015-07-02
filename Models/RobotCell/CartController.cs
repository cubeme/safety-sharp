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

	public class CartController : Component
	{
		private readonly CartEngine _engine;
		private Position _destination;
		private Position _pointOfOrigin;
		private State _state = State.AwaitingReconfiguration;

		public CartController(CartEngine engine)
		{
			_engine = engine;
		}

		public void Reconfigure(Position pointOfOrigin, Position destination)
		{
			_pointOfOrigin = pointOfOrigin;
			_destination = destination;

			_state = State.GetWorkpiece;
		}

		public bool RequiresReconfiguration()
		{
			return _state == State.AwaitingReconfiguration;
		}

		public extern bool IsDone();

		public override void Update()
		{
			switch (_state)
			{
				case State.GetWorkpiece:
					_engine.MoveTo(_pointOfOrigin);
					return;
				case State.GoToDestination:
					_engine.MoveTo(_destination);
					return;
				case State.AwaitCompletion:
					if (IsDone())
						_state = State.GoToDestination;
					return;
			}
		}

		private enum State
		{
			AwaitingReconfiguration,
			GetWorkpiece,
			GoToDestination,
			AwaitCompletion,
			Done
		}
	}
}