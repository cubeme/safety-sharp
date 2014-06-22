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
open SafetySharp.CSharp.Extensions

/// Represents a callback that emits a diagnostic.
type DiagnosticCallback = delegate of locationNode : SyntaxNode * [<ParamArray>] messageArgs : obj array -> unit

/// A base class for syntax node analyzers.
[<AbstractClass>]
type SyntaxNodeAnalyzer<'T when 'T :> CSharpSyntaxNode> () =
    inherit CSharpAnalyzer ()

    interface ISyntaxTreeAnalyzer with
        override this.AnalyzeSyntaxTree (syntaxTree, addDiagnostic, cancellationToken) =
            nullArg syntaxTree "syntaxTree"
            nullArg addDiagnostic "addDiagnostic"

            let diagnosticCallback = DiagnosticCallback (fun locationNode args ->
                addDiagnostic.Invoke (Diagnostic.Create (this.descriptor, locationNode.GetLocation (), args)))
    
            // Roslyn's AnalyzerDriver is going to swallow all exceptions that might be raised -- that is ok, as long as we
            // report them as an error.
            try
                syntaxTree.DescendantsAndSelf<'T>()
                |> Seq.iter (fun node -> this.Analyze node diagnosticCallback cancellationToken)
            with
            | e -> Log.Error "%s" e.Message

    ///  Analyzes the <paramref name="syntaxNode"/>.
    abstract member Analyze : syntaxNode : 'T -> addDiagnostic : DiagnosticCallback -> cancellationToken : CancellationToken -> unit