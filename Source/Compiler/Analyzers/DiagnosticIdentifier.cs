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

namespace SafetySharp.Compiler.Analyzers
{
	using System;
	using Roslyn;

	/// <summary>
	///     Represents a unique identifier for a S# diagnostic emitted by a <see cref="Analyzer" />.
	/// </summary>
	public enum DiagnosticIdentifier
	{
		// Type diagnostics
		CustomComponent = 1000,
		ComponentInterfaceReimplementation,
		ExplicitEnumType,
		ExplicitEnumMemberValue,
		InvalidUpdateCall,

		// Fault diagnostics
		MissingOccurrencePattern = 2000,
		AmbiguousOccurrencePattern,
		OccurrencePatternHasNoEffect,
		NonOccurrencePatternType,
		FaultEffectUnknownMethod,
		FaultEffectUnknownProperty,
		FaultEffectAmbiguousMember,
		FaultEffectBaseMember,
		FaultEffectOptionalParameter,
		UnsupportedFaultInheritance,
		FaultWithoutEffects,
		FaultOutsideComponent,
		GenericFaultDeclaration,

		// Port diagnostics
		AmbiguousPortKind = 3000,
		UnknownProvidedPort,
		UnknownRequiredPort,
		VirtualRequiredPort,
		OverrideRequiredPort,
		StaticPort,
		UnmarkedInterfacePort,
		PortPropertyAccessor,
		ProvidedPortImplementedAsRequiredPort,
		RequiredPortImplementedAsProvidedPort,
		NonExternRequiredPort,
		UpdateMethodMarkedAsPort,
		ExternProvidedPort,
		ExternUpdateMethod,
		InaccessibleProvidedPort,
		InaccessibleRequiredPort,

		// Binding diagnostics
		AmbiguousBinding = 4000,
		BindingFailure,
		ExpectedPortAssignment,
		ExpectedPortReference,
		ExpectedPortDelegateCast,
		ExplicitPortBindingInstantiation,

		// Misc diagnostics
		ReservedName = 9000,
		Recursion,
		MutualRecursion
	}
}