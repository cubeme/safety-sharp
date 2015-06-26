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

namespace Tests.Diagnostics.PortReferences.Invalid
{
	using System;
	using SafetySharp.Compiler.Analyzers;
	using SafetySharp.Modeling;

	[Diagnostic(DiagnosticIdentifier.UnknownRequiredPort, 34, 35, 3, "Tests.Diagnostics.PortReferences.Invalid.X1", "Xyz")]
	internal class X1 : Component
	{
		private X1()
		{
			var x = RequiredPorts.Xyz;
		}
	}

	[Diagnostic(DiagnosticIdentifier.UnknownRequiredPort, 43, 40, 3, "Tests.Diagnostics.PortReferences.Invalid.X2", "Xyz")]
	internal class X2 : Component
	{
		private X2()
		{
			var x = this.RequiredPorts.Xyz;
		}
	}

	[Diagnostic(DiagnosticIdentifier.UnknownRequiredPort, 52, 37, 3, "Tests.Diagnostics.PortReferences.Invalid.X3", "Xyz")]
	internal class X3 : Component
	{
		private X3(X3 x)
		{
			var y = x.RequiredPorts.Xyz;
		}
	}

	[Diagnostic(DiagnosticIdentifier.UnknownRequiredPort, 62, 37, 3, "Tests.Diagnostics.PortReferences.Invalid.X4", "Xyz")]
	internal class X4 : Component
	{
		private X4()
		{
			X4 x = null;
			var y = x.RequiredPorts.Xyz;
		}
	}

	[Diagnostic(DiagnosticIdentifier.UnknownRequiredPort, 73, 37, 3, "Tests.Diagnostics.PortReferences.Invalid.X5", "Xyz")]
	internal class X5 : Component
	{
		private X5 x;

		private X5()
		{
			var y = x.RequiredPorts.Xyz;
		}
	}

	[Diagnostic(DiagnosticIdentifier.UnknownRequiredPort, 82, 37, 3, "Tests.Diagnostics.PortReferences.Invalid.X6", "Xyz")]
	internal class X6 : Component
	{
		private X6()
		{
			var y = x.RequiredPorts.Xyz;
		}

		private X6 x { get; set; }
	}

	[Diagnostic(DiagnosticIdentifier.UnknownRequiredPort, 93, 39, 3, "Tests.Diagnostics.PortReferences.Invalid.X7", "Xyz")]
	internal class X7 : Component
	{
		private X7()
		{
			var y = x().RequiredPorts.Xyz;
		}

		private X7 x()
		{
			return null;
		}
	}

	internal class Y1 : Component
	{
	}

	[Diagnostic(DiagnosticIdentifier.UnknownRequiredPort, 111, 37, 3, "Tests.Diagnostics.PortReferences.Invalid.Y1", "Xyz")]
	internal class X8 : Component
	{
		private X8(Y1 y)
		{
			var z = y.RequiredPorts.Xyz;
		}

		private extern void Xyz();
	}

	[Diagnostic(DiagnosticIdentifier.UnknownRequiredPort, 122, 37, 3, "SafetySharp.Modeling.Component", "Xyz")]
	internal class X9 : Component
	{
		private X9(Component y)
		{
			var z = y.RequiredPorts.Xyz;
		}
	}

	[Diagnostic(DiagnosticIdentifier.UnknownRequiredPort, 131, 37, 3, "SafetySharp.Modeling.IComponent", "Xyz")]
	internal class X10 : Component
	{
		private X10(IComponent y)
		{
			var z = y.RequiredPorts.Xyz;
		}
	}

	internal interface I1 : IComponent
	{
	}

	[Diagnostic(DiagnosticIdentifier.UnknownRequiredPort, 144, 37, 3, "Tests.Diagnostics.PortReferences.Invalid.I1", "Xyz")]
	internal class X11 : Component
	{
		private X11(I1 y)
		{
			var z = y.RequiredPorts.Xyz;
		}

		private extern void Xyz();
	}
}