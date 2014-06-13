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

namespace SafetySharp.CSharp.Diagnostics

open System
open System.Collections.Immutable
open System.Threading
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Diagnostics
open SafetySharp.Utilities

/// Ensures that no enumeration members explicitly declare a constant value.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.IllegalEnumMemberValue, LanguageNames.CSharp)>]
type EnumMemberAnalyzer () as this =
    inherit SyntaxNodeAnalyzer<EnumMemberDeclarationSyntax> ()

    do this.Error DiagnosticIdentifiers.IllegalEnumMemberValue
        "Values of enumeration members must not be explicitly declared."
        "Value of enum member '{0}' cannot be declared explicitly."

    override this.Analyze syntaxNode addDiagnostic cancellationToken = 
        if syntaxNode.EqualsValue <> null then
            addDiagnostic.Invoke (syntaxNode.EqualsValue.Value, syntaxNode.Identifier.ValueText)

    