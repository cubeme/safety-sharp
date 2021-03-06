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

namespace Tests.Diagnostics.PortKinds.Valid
{
	using System;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;

	internal interface R1
	{
		void M();
	}

	internal interface R2
	{
		int M { get; set; }
	}

	internal class R3 : Component
	{
		private void M()
		{
		}
	}

	internal class R4 : Component
	{
		private int M { get; set; }
	}

	internal class R5
	{
		private void M()
		{
		}
	}

	internal class R6
	{
		private int M { get; set; }
	}

	internal class R7 : IComponent
	{
		public dynamic RequiredPorts { get; private set; }
		public dynamic ProvidedPorts { get; private set; }

		public void Update()
		{
		}

		public bool IsMetadataFinalized { get; private set; }
		public ObjectMetadata Metadata { get; private set; }

		private void M()
		{
		}
	}

	internal class R8 : IComponent
	{
		private int M { get; set; }
		public dynamic RequiredPorts { get; private set; }
		public dynamic ProvidedPorts { get; private set; }

		public void Update()
		{
		}

		public bool IsMetadataFinalized { get; private set; }
		public ObjectMetadata Metadata { get; private set; }
	}
}