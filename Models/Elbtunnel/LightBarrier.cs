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

namespace Elbtunnel
{
	using System;
	using System.Diagnostics;
	using SafetySharp.Modeling;
	using SharedComponents;

	internal interface ISensor : IComponent
	{
		[Required]
		void SendData(int position);

		[Provided]
		bool IsTriggered();
	}

	internal class InterfacedSubcomponent : Component
	{
		private readonly LightBarrier _sensor;
		private bool _triggered;

		public InterfacedSubcomponent(LightBarrier sensor)
		{
			_sensor = sensor;
		}

		public override void Update()
		{
			_sensor.IsTriggered(out _triggered);
		}
	}

	class Generic2<T>: GenericComponent<T>
	{
		private GenericComponent<T> c1;
		private GenericComponent<bool> c2;

		public Generic2(params T[] v) : base(v)
		{
			c1 = new GenericComponent<T>(v);
			c2 = new GenericComponent<bool>(false, false, false);
		}
	}

	class GenericComponent<T> : Component
	{
		T f;

		public GenericComponent(params T[] values)
		{
			SetInitialValues(()=>f, values);
		}

		public T MyPort(T val)
		{
			return val;
		}
	}

	internal delegate void D(ref int i);
	public class LightBarrier : Component
	{
		private int _i = 1;
		public bool Triggered = false;
		private Timer _timer;
		public LightBarrier(Timer timer)
		{
			_timer = timer;
			BindDelayed(_timer.RequiredPorts.Test = ProvidedPorts.Do);
			BindDelayed(RequiredPorts.SendData = (D)ProvidedPorts.SendProvided);
			BindDelayed(RequiredPorts.SendData = (D)ProvidedPorts.SendProvided);
			BindDelayed(RequiredPorts.SendData = ProvidedPorts.SendProvided33);
			BindInstantaneous(RequiredPorts.SendData = (Action<int>)ProvidedPorts.SendProvided);
			BindInstantaneous(RequiredPorts.GetPort = ProvidedPorts.IsTriggered);
		}

		[Required]
		public extern void SendData(int position);

		[Required]
		public extern void SendData(ref int position);

		public extern int GetPort(out bool position);

		void SendProvided(ref int position)
		{
			
		}
		void SendProvided(int position)
		{

		}
		void SendProvided33(int position)
		{

		}

		public int IsTriggered(out bool t)
		{
			_timer.Update();
			t= false;
			return 0;
		}

		[Provided]
		public void Do()
		{
			SendData(22);
			var q = 38;
			//q = Choose.Value(23, 4, 23, 55);
			if (_i == 3)
			{
				_i = _i + 1 + (Triggered ? 1 : 0) + GetPort(out Triggered);
				q += 3;
			}
			else
				--_i;
			//return _i + q;
			_i *= q;
		}
	}

	internal enum Lane
	{
		Left,
		Right
	}

	internal class Test2 : Component
	{
		public readonly BooleanComponent Boolean2;
		private BooleanComponent _boolean1;

		public Test2()
		{
			_boolean1 = new BooleanComponent(true);
			Boolean2 = new BooleanComponent(false);
		}
	}

	internal class BooleanComponent : Component
	{
		public Lane Lane = Lane.Right;
		public bool Value;

		public BooleanComponent(bool nondeterministicInitialValue)
		{
			if (nondeterministicInitialValue)
				SetInitialValues(Value, true, false);
			else
				Value = false;
			//SetInitialValues(Lane, Lane.Right, Lane.Left);
			//Update();
			//Bind(Q2, Provided);
		}

		public extern void Test(); // ---> public Action Test { private get; set; }
		protected internal extern int Q();
		protected internal extern int Q2(bool f);

		private int Provided(bool f)
		{
			int x = 0;
			return x;
		}

		[DebuggerNonUserCode]
		[DebuggerHidden]
		[Required]
		private extern void P(int a,
							  int b);

		public override void Update()
		{
			Lane = Lane.Left;
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