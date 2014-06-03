﻿// The MIT License (MIT)
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
	using SafetySharp.Modeling;

	public class LightBarrier : Component
	{
		public bool Triggered;

		public int Do()
		{
			return 1;
		}
	}

	/// <summary>
	///     This is a great interface.
	/// </summary>
	internal interface MyInterface
	{
	}

	internal class Test2 : Component
	{
		private BooleanComponent boolean1 ;
		private BooleanComponent boolean2 ;

		public Test2()
		{
			boolean1 = new BooleanComponent(true);
			boolean2 = new BooleanComponent(false);
		}
	}

	internal class BooleanComponent : Component
	{
		private bool _value;

		public BooleanComponent(bool nondeterministicInitialValue)
		{
			if (nondeterministicInitialValue)
				SetInitialValues(() => _value, true, false);
			else
				_value = false;

			sbyte i = 0;
			i++;
		}

		protected override void Update()
		{
			_value = Choose(true, false);
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