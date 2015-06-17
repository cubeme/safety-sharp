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

namespace Tests.Diagnostics.CustomComponents.Invalid
{
	using System;
	using SafetySharp.Compiler.Analyzers;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;

	internal class W5
	{
		[Diagnostic(DiagnosticIdentifier.CustomComponent, 33, 23, 2, "Tests.Diagnostics.CustomComponents.Invalid.W5.W6")]
		private class W6 : IComponent
		{
			public dynamic RequiredPorts { get; private set; }
			public dynamic ProvidedPorts { get; private set; }

			public void Update()
			{
			}

			public bool IsMetadataFinalized { get; private set; }
			public ObjectMetadata Metadata { get; private set; }
		}
	}

	internal class W7 : Component
	{
		[Diagnostic(DiagnosticIdentifier.CustomComponent, 50, 23, 2, "Tests.Diagnostics.CustomComponents.Invalid.W7.W8")]
		private class W8 : IComponent
		{
			public dynamic RequiredPorts { get; private set; }
			public dynamic ProvidedPorts { get; private set; }

			public void Update()
			{
			}

			public bool IsMetadataFinalized { get; private set; }
			public ObjectMetadata Metadata { get; private set; }
		}
	}
}