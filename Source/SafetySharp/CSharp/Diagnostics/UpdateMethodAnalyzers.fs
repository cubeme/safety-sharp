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
open SafetySharp.Modeling
open SafetySharp.Internal.CSharp.Roslyn

/// Ensures that the return type of a component update method is <see cref="System.Void" />.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.ReturnTypeOfUpdateMethodMustBeVoid, LanguageNames.CSharp)>]
type internal UpdateMethodReturnTypeAnalyzer () as this =
    inherit SymbolAnalyzer<IMethodSymbol> (SymbolKind.Method)

    let message = sprintf "A method marked with '%s' must have a 'void' return type." typeof<BehaviorAttribute>.FullName
    do this.Error DiagnosticIdentifiers.ReturnTypeOfUpdateMethodMustBeVoid message message        

    override this.Analyze methodSymbol compilation addDiagnostic cancellationToken = 
        let withinComponent = methodSymbol.ContainingType.IsDerivedFromComponent compilation
        let hasNonVoidReturnType = methodSymbol.IsUpdateMethod compilation && not methodSymbol.ReturnsVoid 
        if withinComponent && hasNonVoidReturnType then
            addDiagnostic.Invoke methodSymbol

/// Ensures that a component update method has no parameters.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.UpdateMethodCannotHaveParameters, LanguageNames.CSharp)>]
type internal UpdateMethodParameterAnalyzer () as this =
    inherit SymbolAnalyzer<IMethodSymbol> (SymbolKind.Method)

    let message = sprintf "A method marked with '%s' cannot have any parameters." typeof<BehaviorAttribute>.FullName
    do this.Error DiagnosticIdentifiers.UpdateMethodCannotHaveParameters message message        

    override this.Analyze methodSymbol compilation addDiagnostic cancellationToken =   
        let withinComponent = methodSymbol.ContainingType.IsDerivedFromComponent compilation
        let hasParameters = methodSymbol.IsUpdateMethod compilation && methodSymbol.Parameters.Length <> 0
        if withinComponent && hasParameters then
            addDiagnostic.Invoke methodSymbol

/// Ensures that a component declares only one update method.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.MultipleUpdateMethods, LanguageNames.CSharp)>]
type internal MultipleUpdateMethodsAnalyzer () as this =
    inherit SymbolAnalyzer<ITypeSymbol> (SymbolKind.NamedType)

    let message = sprintf "A component can only mark one method with '%s'." typeof<BehaviorAttribute>.FullName
    do this.Error DiagnosticIdentifiers.MultipleUpdateMethods message message        

    override this.Analyze typeSymbol compilation addDiagnostic cancellationToken = 
        if typeSymbol.TypeKind = TypeKind.Class && typeSymbol.IsDerivedFromComponent compilation then
            let updateMethods = 
                typeSymbol.GetMembers().OfType<IMethodSymbol> ()
                |> Seq.where (fun method' -> method'.IsUpdateMethod compilation)
                |> Array.ofSeq

            if updateMethods.Length > 1 then
                for updateMethod in updateMethods do
                    addDiagnostic.Invoke updateMethod

/// Ensures that a component update method has a body and is therefore neither extern nor abstract.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.UpdateMethodWithoutBody, LanguageNames.CSharp)>]
type internal UpdateMethodWithoutBodyAnalyzer () as this =
    inherit SymbolAnalyzer<IMethodSymbol> (SymbolKind.Method)

    let message = sprintf "A method marked with '%s' must define a body and cannot be extern or abstract." typeof<BehaviorAttribute>.FullName
    do this.Error DiagnosticIdentifiers.UpdateMethodWithoutBody message message        

    override this.Analyze methodSymbol compilation addDiagnostic cancellationToken = 
        let withinComponent = methodSymbol.ContainingType.IsDerivedFromComponent compilation
        if withinComponent && methodSymbol.IsUpdateMethod compilation then
            let hasBody = 
                methodSymbol.DeclaringSyntaxReferences 
                |> Seq.map (fun reference -> reference.GetSyntax () :?> MethodDeclarationSyntax)
                |> Seq.map (fun methodDeclaration -> methodDeclaration.Body)
                |> Seq.where ((<>) null)
                |> Seq.length <> 0
            if not hasBody then
                addDiagnostic.Invoke methodSymbol