// The MIT License (MIT)
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

namespace SafetySharp.CSharp

open System
open System.Collections.Immutable
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.Diagnostics
open SafetySharp.Utilities

/// A base class for C# code analyzers.
[<AbstractClass>]
type CSharpAnalyzer () =

    /// The descriptor for the diagnostic emitted by the analyzer.
    [<DefaultValue>] val mutable descriptor : DiagnosticDescriptor

    /// The set of descriptors for the diagnostics that this analyzer is capable of producing.
    [<DefaultValue>] val mutable supportedDiagnostics : ImmutableArray<DiagnosticDescriptor>

    /// Describes the error diagnostic of the analyzer.
    member this.Error identifier description messageFormat =
        this.SetDescriptor identifier description messageFormat DiagnosticSeverity.Error

    /// Describes the error diagnostic of the analyzer.
    member this.Warning identifier description messageFormat =
        this.SetDescriptor identifier description messageFormat DiagnosticSeverity.Warning

    /// Describes the error diagnostic of the analyzer.
    member private this.SetDescriptor identifier description messageFormat severity =
        Requires.That (this.descriptor = null) "A descriptor has already been set."
        Requires.NotNullOrWhitespace identifier "identifier"
        Requires.NotNullOrWhitespace description "description"
        Requires.NotNullOrWhitespace messageFormat "messageFormat"
        Requires.ArgumentSatisfies (identifier.StartsWith DiagnosticIdentifiers.Prefix) "identifier"
            (sprintf "Diagnostic identifier does not start with prefix '%s'." DiagnosticIdentifiers.Prefix)

        this.descriptor <- DiagnosticDescriptor (identifier, description, messageFormat, DiagnosticIdentifiers.Category, severity, true)
        this.supportedDiagnostics <- ImmutableArray.Create this.descriptor

    interface IDiagnosticAnalyzer with
        /// Returns a set of descriptors for the diagnostics that this analyzer is capable of producing.
        member this.SupportedDiagnostics = this.supportedDiagnostics
        