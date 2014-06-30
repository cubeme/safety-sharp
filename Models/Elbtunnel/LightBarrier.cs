// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

namespace Elbtunnel
{
	using System;
	using System.Diagnostics;
	using SafetySharp.Modeling;

	public class LightBarrier : Component
	{
		public bool Triggered = false;
		private int _i = 1;
		
		public int Do()
		{
			var q = 38;
			q = Choose.Value(23, 4, 23, 55);
			_i = _i + 1;
			return _i + q;
		}
	}


	internal class Test2 : Component
	{
		private BooleanComponent _boolean1;
		public readonly BooleanComponent Boolean2;

		public Test2()
		{
			_boolean1 = new BooleanComponent(true);
			Boolean2 = new BooleanComponent(false);
		}
	}

	internal class BooleanComponent : Component
	{
		public bool Value;

		public BooleanComponent(bool nondeterministicInitialValue)
		{
			if (nondeterministicInitialValue)
				SetInitialValues(Value, true, false);
			else
				Value = false;

			//Update();
			//Bind(Q2, Provided);
		}

		public extern void Test(); // ---> public Action Test { private get; set; }

		protected internal extern  int Q();
		protected internal extern  int Q2(bool f);

		int Provided(bool f)
		{
			int x = 0;
			return 0;
		}

			[DebuggerNonUserCode]

		[DebuggerHidden]
		private extern void P(int a, 
				
				int b);
		 
		protected override void Update()
		{
			Value = Choose.Boolean();
			if (Value == false)
				Value = true;
			else if (!Value)
				Value = false;
			else
			{
				Value = true || false;
				Value = !Value;
			}
		}
	}

	internal enum Test
	{
	}

	//public enum MyEnum : short
	//{
	//	ValueA,
	//	ValueB,
	//	ValueC = 10,
	//	ValueCQ = 104,
	//	ValueCQ2 = ValueCQ + 1,
	//	ValueCF
	//}
}