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

namespace Tests.Diagnostics.FaultEffects.Valid
{
	using System;
	using SafetySharp.Modeling;
	using SafetySharp.Modeling.Faults;

	internal interface I2 : IComponent
	{
		[Provided]
		void InterfaceMethod();
	}

	internal class X2 : Component, I2
	{
		void I2.InterfaceMethod()
		{
			throw new NotImplementedException();
		}

		public void Void2Void()
		{
		}

		public int Int2Int(int a)
		{
			return a;
		}

		private void Overloaded(int b)
		{
		}

		public void Overloaded()
		{
		}

		protected void Overloaded(bool d)
		{
		}

		internal void Ref(ref int q)
		{
		}

		public void Out(out int q)
		{
			q = 1;
		}

		[Transient]
		private class F : Fault
		{
			public void InterfaceMethod()
			{
			}

			public void Void2Void()
			{
			}

			public int Int2Int(int a)
			{
				return a;
			}

			public void Overloaded(int b)
			{
			}

			public void Overloaded()
			{
			}

			public void Overloaded(bool d)
			{
			}

			public void Ref(ref int q)
			{
			}

			public void Out(out int q)
			{
				q = 1;
			}
		}
	}
}