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

namespace SafetySharp.CSharp.Analyzers
{
	using System;
	using Roslyn;

	/// <summary>
	///     Represents a unique identifier for a S# diagnostic emitted by a <see cref="CSharpAnalyzer" />.
	/// </summary>
	public enum DiagnosticIdentifier
	{
		// Type diagnostics
		CustomComponent = 1000,
		ExplicitEnumType = 1001,
		ExplicitEnumMemberValue = 1002,

		// Fault diagnostics
		MissingOccurrencePattern = 2000,
		AmbiguousOccurrencePattern = 2001,
		OccurrencePatternHasNoEffect = 2002,

		// Port diagnostics
		AmbiguousPortKind = 3000,
		UnknownProvidedPort = 3001,
		UnknownRequiredPort = 3002,
		UnmarkedInterfacePort = 3003,
		PortPropertyAccessor = 3004,
		ProvidedPortImplementedAsRequiredPort = 3005,
		RequiredPortImplementedAsProvidedPort = 3006,
		NonExternRequiredPort = 3007,
		ExternProvidedPort = 3008,

		// Binding diagnostics
		AmbiguousBinding = 4000,
		BindingFailure = 4001,

		// Misc diagnostics
		ReservedName = 9000
	}
}