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

namespace ProductionCell
{
	using SafetySharp.Modeling;

	public class Robot : Component
	{
		private readonly Tool _drillTool;
		private readonly Tool _insertTool;
		private readonly WorkpieceSensor _sensor;
		private readonly Tool _tightenTool;
		private Position _position;
		private State _state = State.AwaitingReconfiguration;
		private RobotTask _task;

		public Robot(Position position, WorkpieceSensor sensor, Tool drillTool, Tool insertTool, Tool tightenTool)
		{
			_position = position;
			_sensor = sensor;
			_drillTool = drillTool;
			_insertTool = insertTool;
			_tightenTool = tightenTool;
		}

		public void Reconfigure(RobotTask task)
		{
			_task = task;
			_state = State.Ready;
		}

		public bool RequiresReconfiguration()
		{
			return _state == State.AwaitingReconfiguration || IsCurrentToolBroken();
		}

		private bool IsCurrentToolBroken()
		{
			switch (_task)
			{
				case RobotTask.Drill:
					return _drillTool.IsBroken();
				case RobotTask.Insert:
					return _insertTool.IsBroken();
				case RobotTask.Tighten:
					return _tightenTool.IsBroken();
				default:
					return true;
			}
		}

		public override void Update()
		{
			switch (_state)
			{
				case State.Done:
					_state = State.Ready;
					return;
				case State.Ready:
					if (_sensor.WorkpieceDetected())
						_state = State.Working;
					return;
				case State.Working:
					UseTool();
					_state = IsCurrentToolBroken() ? State.AwaitingReconfiguration : State.Done;
					return;
			}
		}

		private void UseTool()
		{
			switch (_task)
			{
				case RobotTask.Drill:
					_drillTool.UseTool();
					return;
				case RobotTask.Insert:
					_insertTool.UseTool();
					return;
				case RobotTask.Tighten:
					_tightenTool.UseTool();
					return;
			}
		}

		private enum State
		{
			AwaitingReconfiguration,
			Ready,
			Working,
			Done
		}
	}
}