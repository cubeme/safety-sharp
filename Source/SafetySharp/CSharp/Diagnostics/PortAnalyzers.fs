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

/// Ensures that a method or property is not marked with both the <see cref="ProvidedAttribute" /> and the
/// <see cref="RequiredAttribute" />.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.MarkedWithBothProvidedAndRequiredAttribute, LanguageNames.CSharp)>]
type internal MarkedWithBothProvidedAndRequiredAttributesAnalyzer () as this =
    inherit SymbolAnalyzer<ISymbol> (SymbolKind.Method, SymbolKind.Property)

    do this.Error DiagnosticIdentifiers.MarkedWithBothProvidedAndRequiredAttribute
        (sprintf "A method or property cannot be marked with both '%s' and '%s'." typeof<RequiredAttribute>.FullName typeof<ProvidedAttribute>.FullName)
        (sprintf "'{0}' cannot be marked with both '%s' and '%s'." typeof<RequiredAttribute>.FullName typeof<ProvidedAttribute>.FullName)

    override this.Analyze symbol compilation addDiagnostic cancellationToken = 
        if symbol.ContainingType.ImplementsIComponent compilation then
            match symbol with
            | :? IMethodSymbol as methodSymbol when not (methodSymbol.AssociatedSymbol :? IPropertySymbol) ->
                let hasRequiredAttribute = methodSymbol.HasAttribute<RequiredAttribute> compilation
                let hasProvidedAttribute = methodSymbol.HasAttribute<ProvidedAttribute> compilation
                if hasProvidedAttribute && hasRequiredAttribute then
                    addDiagnostic.Invoke (methodSymbol, methodSymbol.ToDisplayString ())
            | :? IPropertySymbol as propertySymbol ->
                let hasRequiredAttribute = propertySymbol.HasAttribute<RequiredAttribute> compilation
                let hasProvidedAttribute = propertySymbol.HasAttribute<ProvidedAttribute> compilation
                if hasProvidedAttribute && hasRequiredAttribute then
                    addDiagnostic.Invoke (propertySymbol, propertySymbol.ToDisplayString ())
            | _ -> ()

/// Ensures that a method or property marked with the <see cref="ProvidedAttribute" /> is not extern.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.ExternProvidedPort, LanguageNames.CSharp)>]
type internal ExternProvidedPortAnalyzer () as this =
    inherit SymbolAnalyzer<ISymbol> (SymbolKind.Method, SymbolKind.Property)

    do this.Error DiagnosticIdentifiers.ExternProvidedPort
        (sprintf "A method or property marked with '%s' cannot be extern." typeof<ProvidedAttribute>.FullName)
        (sprintf "'{0}' marked with '%s' cannot be extern." typeof<ProvidedAttribute>.FullName)

    override this.Analyze symbol compilation addDiagnostic cancellationToken = 
        if symbol.ContainingType.IsDerivedFromComponent compilation then
            match symbol with
            | :? IMethodSymbol as methodSymbol when not (methodSymbol.AssociatedSymbol :? IPropertySymbol) ->
                let hasProvidedAttribute = methodSymbol.HasAttribute<ProvidedAttribute> compilation
                if hasProvidedAttribute && methodSymbol.IsExtern then
                    addDiagnostic.Invoke (methodSymbol, methodSymbol.ToDisplayString ())
            | :? IPropertySymbol as propertySymbol ->
                let hasProvidedAttribute = propertySymbol.HasAttribute<ProvidedAttribute> compilation
                if hasProvidedAttribute && propertySymbol.IsExtern then
                    addDiagnostic.Invoke (propertySymbol, propertySymbol.ToDisplayString ())
            | _ -> ()

/// Ensures that a method or property marked with the <see cref="RequiredAttribute" /> is extern.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.NonExternRequiredPort, LanguageNames.CSharp)>]
type internal NonExternRequiredPortAnalyzer () as this =
    inherit SymbolAnalyzer<ISymbol> (SymbolKind.Method, SymbolKind.Property)

    do this.Error DiagnosticIdentifiers.NonExternRequiredPort
        (sprintf "A method or property marked with '%s' must be extern." typeof<RequiredAttribute>.FullName)
        (sprintf "'{0}' marked with '%s' must be extern." typeof<RequiredAttribute>.FullName)

    override this.Analyze symbol compilation addDiagnostic cancellationToken = 
        if symbol.ContainingType.IsDerivedFromComponent compilation then
            match symbol with
            | :? IMethodSymbol as methodSymbol when not (methodSymbol.AssociatedSymbol :? IPropertySymbol) ->
                let hasRequiredAttribute = methodSymbol.HasAttribute<RequiredAttribute> compilation
                if hasRequiredAttribute && not methodSymbol.IsExtern then
                    addDiagnostic.Invoke (methodSymbol, methodSymbol.ToDisplayString ())
            | :? IPropertySymbol as propertySymbol ->
                let hasRequiredAttribute = propertySymbol.HasAttribute<RequiredAttribute> compilation
                if hasRequiredAttribute && not propertySymbol.IsExtern then
                    addDiagnostic.Invoke (propertySymbol, propertySymbol.ToDisplayString ())
            | _ -> ()

/// Ensures that a method or property within an interface derived from <see cref="IComponent" /> is marked with either
/// the <see cref="RequiredAttribute" /> or <see cref="PortAttribute" />.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.ComponentInterfaceMethodWithoutPortAttribute, LanguageNames.CSharp)>]
type internal ComponentInterfaceMethodWithoutPortAttributeAnalyzer () as this =
    inherit SymbolAnalyzer<ISymbol> (SymbolKind.Method, SymbolKind.Property)

    do this.Error DiagnosticIdentifiers.ComponentInterfaceMethodWithoutPortAttribute
        (sprintf "A method or property within a component interface must be marked with either '%s' or '%s'." 
            typeof<RequiredAttribute>.FullName typeof<ProvidedAttribute>.FullName)
        (sprintf "'{0}' must be marked with either '%s' or '%s'."
            typeof<RequiredAttribute>.FullName typeof<ProvidedAttribute>.FullName)

    override this.Analyze symbol compilation addDiagnostic cancellationToken = 
        if symbol.ContainingType.TypeKind = TypeKind.Interface && symbol.ContainingType.ImplementsIComponent compilation then
            match symbol with
            | :? IMethodSymbol as methodSymbol when not (methodSymbol.AssociatedSymbol :? IPropertySymbol) ->
                let hasRequiredAttribute = methodSymbol.HasAttribute<RequiredAttribute> compilation
                let hasProvidedAttribute = methodSymbol.HasAttribute<ProvidedAttribute> compilation
                if not hasProvidedAttribute && not hasRequiredAttribute then
                    addDiagnostic.Invoke (methodSymbol, methodSymbol.ToDisplayString ())
            | :? IPropertySymbol as propertySymbol ->
                let hasRequiredAttribute = propertySymbol.HasAttribute<RequiredAttribute> compilation
                let hasProvidedAttribute = propertySymbol.HasAttribute<ProvidedAttribute> compilation
                if not hasProvidedAttribute && not hasRequiredAttribute then
                    addDiagnostic.Invoke (propertySymbol, propertySymbol.ToDisplayString ())
            | _ -> ()

/// Ensures that a method or property within an interface derived from <see cref="IComponent" /> is marked with either
/// the <see cref="RequiredAttribute" /> or <see cref="PortAttribute" />.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.AccessorIsMakredWithPortAttribute, LanguageNames.CSharp)>]
type internal AccessorIsMakredWithPortAttributeAnalyzer () as this =
    inherit SymbolAnalyzer<ISymbol> (SymbolKind.Method, SymbolKind.Property)

    do this.Error DiagnosticIdentifiers.AccessorIsMakredWithPortAttribute
        (sprintf "An accessor cannot be marked with '%s' or '%s'." 
            typeof<RequiredAttribute>.FullName typeof<ProvidedAttribute>.FullName)
        (sprintf "'{0}' cannot be marked with '%s' or '%s'. Apply the attribute to the property instead."
            typeof<RequiredAttribute>.FullName typeof<ProvidedAttribute>.FullName)

    override this.Analyze symbol compilation addDiagnostic cancellationToken = 
        if symbol.ContainingType.ImplementsIComponent compilation then
            match symbol with
            | :? IMethodSymbol as methodSymbol when methodSymbol.MethodKind = MethodKind.PropertyGet || methodSymbol.MethodKind = MethodKind.PropertySet ->
                let hasRequiredAttribute = methodSymbol.HasAttribute<RequiredAttribute> compilation
                let hasProvidedAttribute = methodSymbol.HasAttribute<ProvidedAttribute> compilation
                if hasProvidedAttribute || hasRequiredAttribute then
                    addDiagnostic.Invoke (methodSymbol, methodSymbol.ToDisplayString ())
            | _ -> ()