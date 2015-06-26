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

	[Diagnostic(DiagnosticIdentifier.UnknownProvidedPort, 34, 35, 3, "Tests.Diagnostics.PortReferences.Invalid.X20", "Xyz")]
	internal class X20 : Component
	{
		private X20()
		{
			var x = ProvidedPorts.Xyz;
		}
	}

	[Diagnostic(DiagnosticIdentifier.UnknownProvidedPort, 43, 40, 3, "Tests.Diagnostics.PortReferences.Invalid.X21", "Xyz")]
	internal class X21 : Component
	{
		private X21()
		{
			var x = this.ProvidedPorts.Xyz;
		}
	}

	[Diagnostic(DiagnosticIdentifier.UnknownProvidedPort, 52, 37, 3, "Tests.Diagnostics.PortReferences.Invalid.X22", "Xyz")]
	internal class X22 : Component
	{
		private X22(X22 x)
		{
			var y = x.ProvidedPorts.Xyz;
		}
	}

	[Diagnostic(DiagnosticIdentifier.UnknownProvidedPort, 62, 37, 3, "Tests.Diagnostics.PortReferences.Invalid.X23", "Xyz")]
	internal class X23 : Component
	{
		private X23()
		{
			X23 x = null;
			var y = x.ProvidedPorts.Xyz;
		}
	}

	[Diagnostic(DiagnosticIdentifier.UnknownProvidedPort, 73, 37, 3, "Tests.Diagnostics.PortReferences.Invalid.X24", "Xyz")]
	internal class X24 : Component
	{
		private X24 x;

		private X24()
		{
			var y = x.ProvidedPorts.Xyz;
		}
	}

	[Diagnostic(DiagnosticIdentifier.UnknownProvidedPort, 82, 37, 3, "Tests.Diagnostics.PortReferences.Invalid.X25", "Xyz")]
	internal class X25 : Component
	{
		private X25()
		{
			var y = x.ProvidedPorts.Xyz;
		}

		private X25 x { get; set; }
	}

	[Diagnostic(DiagnosticIdentifier.UnknownProvidedPort, 93, 39, 3, "Tests.Diagnostics.PortReferences.Invalid.X26", "Xyz")]
	internal class X26 : Component
	{
		private X26()
		{
			var y = x().ProvidedPorts.Xyz;
		}

		private X26 x()
		{
			return null;
		}
	}

	internal class Y8 : Component
	{
	}

	[Diagnostic(DiagnosticIdentifier.UnknownProvidedPort, 111, 37, 3, "Tests.Diagnostics.PortReferences.Invalid.Y8", "Xyz")]
	internal class X27 : Component
	{
		private X27(Y8 y)
		{
			var z = y.ProvidedPorts.Xyz;
		}

		private void Xyz()
		{
		}
	}

	[Diagnostic(DiagnosticIdentifier.UnknownProvidedPort, 124, 37, 3, "SafetySharp.Modeling.Component", "Xyz")]
	internal class X28 : Component
	{
		private X28(Component y)
		{
			var z = y.ProvidedPorts.Xyz;
		}
	}

	[Diagnostic(DiagnosticIdentifier.UnknownProvidedPort, 133, 37, 3, "SafetySharp.Modeling.IComponent", "Xyz")]
	internal class X29 : Component
	{
		private X29(IComponent y)
		{
			var z = y.ProvidedPorts.Xyz;
		}
	}

	internal interface I8 : IComponent
	{
	}

	[Diagnostic(DiagnosticIdentifier.UnknownProvidedPort, 146, 37, 3, "Tests.Diagnostics.PortReferences.Invalid.I8", "Xyz")]
	internal class X30 : Component
	{
		private X30(I8 y)
		{
			var z = y.ProvidedPorts.Xyz;
		}

		private void Xyz()
		{
		}
	}
}