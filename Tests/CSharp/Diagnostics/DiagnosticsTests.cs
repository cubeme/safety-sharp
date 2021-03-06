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

namespace Tests.Diagnostics
{
	using System;
	using Microsoft.CodeAnalysis;
	using SafetySharp.Compiler.Analyzers;
	using Utilities;
	using Xunit;

	public partial class DiagnosticsTests : Tests
	{
		[Theory, MemberData("DiscoverTests", "Bindings")]
		public void Bindings(string test, SyntaxTree code)
		{
			CheckDiagnostics<BindingAnalyzer>(code);
		}

		[Theory, MemberData("DiscoverTests", "Enums")]
		public void Enums(string test, SyntaxTree code)
		{
			CheckDiagnostics<EnumAnalyzer>(code);
		}

		[Theory, MemberData("DiscoverTests", "CustomComponents")]
		public void CustomComponents(string test, SyntaxTree code)
		{
			CheckDiagnostics<CustomComponentAnalyzer>(code);
		}

		[Theory, MemberData("DiscoverTests", "PortKinds")]
		public void PortKinds(string test, SyntaxTree code)
		{
			CheckDiagnostics<PortKindAnalyzer>(code);
		}

		[Theory, MemberData("DiscoverTests", "OccurrencePatterns")]
		public void OccurrencePatterns(string test, SyntaxTree code)
		{
			CheckDiagnostics<OccurrencePatternAnalyzer>(code);
		}

		[Theory, MemberData("DiscoverTests", "Faults")]
		public void Faults(string test, SyntaxTree code)
		{
			CheckDiagnostics<FaultAnalyzer>(code);
		}

		[Theory, MemberData("DiscoverTests", "FaultEffects")]
		public void FaultEffects(string test, SyntaxTree code)
		{
			CheckDiagnostics<FaultEffectAnalyzer>(code);
		}
	}
}