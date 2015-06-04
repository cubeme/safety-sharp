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

namespace Tests.Diagnostics.Enums
{
	using System;
	using SafetySharp.CSharp.Analyzers;

	[Diagnostic(DiagnosticIdentifier.ExplicitEnumType, 29, 24, 4, "Tests.Diagnostics.Enums.E1")]
	internal enum E1 : byte
	{
	}

	[Diagnostic(DiagnosticIdentifier.ExplicitEnumType, 34, 24, 3, "Tests.Diagnostics.Enums.E2")]
	internal enum E2 : int
	{
	}

	[Diagnostic(DiagnosticIdentifier.ExplicitEnumType, 39, 24, 4, "Tests.Diagnostics.Enums.E3")]
	internal enum E3 : long
	{
	}

	[Diagnostic(DiagnosticIdentifier.ExplicitEnumType, 44, 24, 5, "Tests.Diagnostics.Enums.E4")]
	internal enum E4 : sbyte
	{
	}

	[Diagnostic(DiagnosticIdentifier.ExplicitEnumType, 49, 24, 5, "Tests.Diagnostics.Enums.E5")]
	internal enum E5 : short
	{
	}

	[Diagnostic(DiagnosticIdentifier.ExplicitEnumType, 54, 24, 4, "Tests.Diagnostics.Enums.E6")]
	internal enum E6 : uint
	{
	}

	[Diagnostic(DiagnosticIdentifier.ExplicitEnumType, 59, 24, 5, "Tests.Diagnostics.Enums.E7")]
	internal enum E7 : ulong
	{
	}

	[Diagnostic(DiagnosticIdentifier.ExplicitEnumType, 64, 24, 6, "Tests.Diagnostics.Enums.E8")]
	internal enum E8 : ushort
	{
	}
}