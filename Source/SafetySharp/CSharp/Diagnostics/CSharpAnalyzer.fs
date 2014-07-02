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

namespace SafetySharp.Internal.CSharp.Diagnostics

open System
open System.Collections.Immutable
open System.Threading
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Diagnostics
open SafetySharp.Internal.Utilities
open SafetySharp.Internal.CSharp.Roslyn

/// A base class for C# code analyzers.
[<AbstractClass>]
type internal CSharpAnalyzer () =

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
        invalidCall (this.descriptor <> null) "A descriptor has already been set."
        nullOrWhitespaceArg identifier "identifier"
        nullOrWhitespaceArg description "description"
        nullOrWhitespaceArg messageFormat "messageFormat"
        invalidArg (not <| identifier.StartsWith DiagnosticIdentifiers.Prefix) "identifier"
            "Diagnostic identifier does not start with prefix '%s'." DiagnosticIdentifiers.Prefix

        this.descriptor <- DiagnosticDescriptor (identifier, description, messageFormat, DiagnosticIdentifiers.Category, severity, true)
        this.supportedDiagnostics <- ImmutableArray.Create this.descriptor

    interface IDiagnosticAnalyzer with
        /// Returns a set of descriptors for the diagnostics that this analyzer is capable of producing.
        member this.SupportedDiagnostics = this.supportedDiagnostics

/// Represents a callback that emits a diagnostic.
type internal DiagnosticCallback<'T> = delegate of element : 'T * [<ParamArray>] messageArgs : obj array -> unit

/// A base class for syntax node analyzers.
[<AbstractClass>]
type internal SyntaxNodeAnalyzer<'T when 'T :> CSharpSyntaxNode> () =
    inherit CSharpAnalyzer ()

    interface ISyntaxTreeAnalyzer with
        override this.AnalyzeSyntaxTree (syntaxTree, addDiagnostic, cancellationToken) =
            nullArg syntaxTree "syntaxTree"
            nullArg addDiagnostic "addDiagnostic"

            let diagnosticCallback = DiagnosticCallback<SyntaxNode> (fun locationNode args ->
                addDiagnostic.Invoke (Diagnostic.Create (this.descriptor, locationNode.GetLocation (), args)))
    
            syntaxTree.DescendantsAndSelf<'T>()
            |> Seq.iter (fun node -> this.Analyze node diagnosticCallback cancellationToken)

    ///  Analyzes the <paramref name="syntaxNode"/>.
    abstract member Analyze : syntaxNode : 'T -> addDiagnostic : DiagnosticCallback<SyntaxNode> -> cancellationToken : CancellationToken -> unit
   
/// A base class for symbol analyzers.
[<AbstractClass>]
type internal SymbolAnalyzer<'T when 'T :> ISymbol> ([<ParamArray>] symbolKinds : SymbolKind array) =
    inherit CSharpAnalyzer ()

    do nullArg symbolKinds "symbolKinds"
    do invalidArg (symbolKinds.Length = 0) "symbolKinds" "At least one symbol kind must be specified."

    interface ISymbolAnalyzer with
        override this.SymbolKindsOfInterest = 
            ImmutableArray.CreateRange (symbolKinds)

        override this.AnalyzeSymbol (symbol, compilation, addDiagnostic, cancellationToken) =
            nullArg symbol "symbol"
            nullArg addDiagnostic "addDiagnostic"

            let diagnosticCallback = DiagnosticCallback<ISymbol> (fun locationSymbol args ->
                addDiagnostic.Invoke (Diagnostic.Create (this.descriptor, locationSymbol.Locations.[0], args)))
    
            match symbol with
            | :? 'T as symbol -> this.Analyze symbol compilation diagnosticCallback cancellationToken
            | _ -> ()

    ///  Analyzes the <paramref name="symbol"/>.
    abstract member Analyze : symbol : 'T -> compilation : Compilation -> addDiagnostic : DiagnosticCallback<ISymbol> -> cancellationToken : CancellationToken -> unit
        
/// A base class for syntax node analyzers.
[<AbstractClass>]
type internal SemanticModelAnalyzer () =
    inherit CSharpAnalyzer ()

    interface ISemanticModelAnalyzer with
        override this.AnalyzeSemanticModel (semanticModel, addDiagnostic, cancellationToken) =
            nullArg semanticModel "semanticModel"
            nullArg addDiagnostic "addDiagnostic"

            let diagnosticCallback = DiagnosticCallback<SyntaxNode> (fun locationNode args ->
                addDiagnostic.Invoke (Diagnostic.Create (this.descriptor, locationNode.GetLocation (), args)))
    
            this.Analyze semanticModel diagnosticCallback cancellationToken

    ///  Analyzes the <paramref name="syntaxNode"/>.
    abstract member Analyze : semanticModel : SemanticModel -> addDiagnostic : DiagnosticCallback<SyntaxNode> -> cancellationToken : CancellationToken -> unit