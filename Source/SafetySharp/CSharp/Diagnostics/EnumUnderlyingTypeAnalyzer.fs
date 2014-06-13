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

/// Ensures that no enumerations explicitly declare an underlying type.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.IllegalUnderlyingEnumType, LanguageNames.CSharp)>]
type EnumUnderlyingTypeAnalyzer () as this =
    inherit SyntaxNodeAnalyzer<EnumDeclarationSyntax> ()

    do this.Error DiagnosticIdentifiers.IllegalUnderlyingEnumType
        "Enumeration declarations must not explicitly declare an underlying type."
        "Enum '{0}' must not declare an underlying type."

    override this.Analyze syntaxNode addDiagnostic cancellationToken = 
        if syntaxNode.BaseList <> null then
            addDiagnostic.Invoke (syntaxNode.BaseList.Types.First(), syntaxNode.Identifier.ValueText)

    