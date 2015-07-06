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

	public class Environment : Component
	{
		private readonly Cart _cart1 = new Cart();
		private readonly Cart _cart2 = new Cart();
		private readonly Cart _cart3 = new Cart();
		private readonly Cart _cart4 = new Cart();
		private readonly Workpiece _workpiece1 = new Workpiece();
		private readonly Workpiece _workpiece2 = new Workpiece();
		private readonly Workpiece _workpiece3 = new Workpiece();

		public Position GetWorkpiecePosition(int workpiece)
		{
			switch (workpiece)
			{
				case 0:
					return _cart1.GetPosition();
				case 1:
					return _cart2.GetPosition();
				case 2:
					return _cart3.GetPosition();
				case 3:
					return _cart4.GetPosition();
				default:
					return Position.Unknown;
			}
		}

		private int GetWorkpieceAt(Position position)
		{
			return 0;
		}

		public bool ApplyTool(Position position, RobotTask task)
		{
			switch (GetWorkpieceAt(position))
			{
				case 0:
					_workpiece1.ApplyTool(task);
					return true;
				case 1:
					_workpiece2.ApplyTool(task);
					return true;
				case 2:
					_workpiece3.ApplyTool(task);
					return true;
				default:
					return false;
			}
		}
	}
}