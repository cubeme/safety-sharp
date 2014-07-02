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
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.AccessorIsMarkedWithPortAttribute, LanguageNames.CSharp)>]
type internal AccessorIsMarkedWithPortAttributeAnalyzer () as this =
    inherit SymbolAnalyzer<ISymbol> (SymbolKind.Method, SymbolKind.Property)

    do this.Error DiagnosticIdentifiers.AccessorIsMarkedWithPortAttribute
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

/// Ensures that the port attribute specifications of an implementing method or property and the corresponding interface
/// method or property don't contradict.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.ClassPortAttributeContradictsInterfacePortAttribute, LanguageNames.CSharp)>]
type internal ClassPortAttributeContradictsInterfacePortAttributeAnalyzer () as this =
    inherit SymbolAnalyzer<INamedTypeSymbol> (SymbolKind.NamedType)

    do this.Error DiagnosticIdentifiers.ClassPortAttributeContradictsInterfacePortAttribute
        "Method or property does not implement the corresponding interface method or property, as the port attributes are different." 
        "'{0}' does not implement interface member '{1}'. Replace attribute '{2}' with '{3}' to implement the interface member."

    override this.Analyze symbol compilation addDiagnostic cancellationToken = 
        if symbol.TypeKind = TypeKind.Class && symbol.IsDerivedFromComponent compilation then
            for interfaceSymbol in symbol.AllInterfaces |> Seq.where (fun interfaceSymbol -> interfaceSymbol.ImplementsIComponent compilation) do
                for interfaceMember in interfaceSymbol.GetMembers () do
                    let implementingMember = symbol.FindImplementationForInterfaceMember interfaceMember
                    if implementingMember.ContainingType = symbol then
                        match implementingMember with
                        | :? IMethodSymbol as methodSymbol ->
                            let interfaceMethod = interfaceMember :?> IMethodSymbol
                            let interfaceRequiredAttribute = interfaceMethod.HasAttribute<RequiredAttribute> compilation
                            let interfaceProvidedAttribute = interfaceMethod.HasAttribute<ProvidedAttribute> compilation
                            let methodRequiredAttribute = methodSymbol.HasAttribute<RequiredAttribute> compilation
                            let methodProvidedAttribute = methodSymbol.HasAttribute<ProvidedAttribute> compilation
                            if interfaceRequiredAttribute && methodProvidedAttribute then
                                addDiagnostic.Invoke (methodSymbol, methodSymbol.ToDisplayString (), interfaceMethod.ToDisplayString (), 
                                                      typeof<ProvidedAttribute>.FullName, typeof<RequiredAttribute>.FullName)
                            elif interfaceProvidedAttribute && methodRequiredAttribute then
                                addDiagnostic.Invoke (methodSymbol, methodSymbol.ToDisplayString (), interfaceMethod.ToDisplayString (), 
                                                      typeof<RequiredAttribute>.FullName, typeof<ProvidedAttribute>.FullName)
                        | :? IPropertySymbol as propertySymbol ->
                            let interfaceProperty = interfaceMember :?> IPropertySymbol
                            let interfaceRequiredAttribute = interfaceProperty.HasAttribute<RequiredAttribute> compilation
                            let interfaceProvidedAttribute = interfaceProperty.HasAttribute<ProvidedAttribute> compilation
                            let propertyRequiredAttribute = propertySymbol.HasAttribute<RequiredAttribute> compilation
                            let propertyProvidedAttribute = propertySymbol.HasAttribute<ProvidedAttribute> compilation
                            if interfaceRequiredAttribute && propertyProvidedAttribute then
                                addDiagnostic.Invoke (propertySymbol, propertySymbol.ToDisplayString (), interfaceProperty.ToDisplayString (), 
                                                      typeof<ProvidedAttribute>.FullName, typeof<RequiredAttribute>.FullName)
                            elif interfaceProvidedAttribute && propertyRequiredAttribute then
                                addDiagnostic.Invoke (propertySymbol, propertySymbol.ToDisplayString (), interfaceProperty.ToDisplayString (), 
                                                      typeof<RequiredAttribute>.FullName, typeof<ProvidedAttribute>.FullName)
                        | _ -> ()

/// Ensures that a method or property within an interface derived from <see cref="IComponent" /> is marked with either
/// the <see cref="RequiredAttribute" /> or <see cref="PortAttribute" />.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.ExternImplementedProvidedPort, LanguageNames.CSharp)>]
type internal ExternImplementedProvidedPortAnalyzer () as this =
    inherit SymbolAnalyzer<INamedTypeSymbol> (SymbolKind.NamedType)

    do this.Error DiagnosticIdentifiers.ExternImplementedProvidedPort
        "Method or property does not implement the corresponding interface method or property, as a provided port cannot be declared 'extern'." 
        "'{0}' does not implement interface member '{1}'. A provided port cannot be declared 'extern'."

    override this.Analyze symbol compilation addDiagnostic cancellationToken = 
        if symbol.TypeKind = TypeKind.Class && symbol.IsDerivedFromComponent compilation then
            for interfaceSymbol in symbol.AllInterfaces |> Seq.where (fun interfaceSymbol -> interfaceSymbol.ImplementsIComponent compilation) do
                for interfaceMember in interfaceSymbol.GetMembers () do
                    let implementingMember = symbol.FindImplementationForInterfaceMember interfaceMember
                    if implementingMember.ContainingType = symbol then
                        match implementingMember with
                        | :? IMethodSymbol as methodSymbol ->
                            let interfaceMethodSymbol = interfaceMember :?> IMethodSymbol
                            let hasProvidedAttribute = interfaceMethodSymbol.HasAttribute<ProvidedAttribute> compilation
                            if hasProvidedAttribute && methodSymbol.IsExtern then
                                addDiagnostic.Invoke (methodSymbol, methodSymbol.ToDisplayString (), interfaceMember.ToDisplayString ())
                        | :? IPropertySymbol as propertySymbol ->
                            let interfacePropertySymbol = interfaceMember :?> IPropertySymbol
                            let hasProvidedAttribute = interfacePropertySymbol.HasAttribute<ProvidedAttribute> compilation
                            if hasProvidedAttribute && propertySymbol.IsExtern then
                                addDiagnostic.Invoke (propertySymbol, propertySymbol.ToDisplayString (), interfaceMember.ToDisplayString ())
                        | _ -> ()

/// Ensures that a method or property within an interface derived from <see cref="IComponent" /> is marked with either
/// the <see cref="RequiredAttribute" /> or <see cref="PortAttribute" />.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.NonExternImplementedRequiredPort, LanguageNames.CSharp)>]
type internal NonExternImplementedRequiredPortAnalyzer () as this =
    inherit SymbolAnalyzer<INamedTypeSymbol> (SymbolKind.NamedType)

    do this.Error DiagnosticIdentifiers.NonExternImplementedRequiredPort
        "Method or property does not implement the corresponding interface method or property, as a required port must be declared 'extern'." 
        "'{0}' does not implement interface member '{1}'. A required port must be declared 'extern'."

    override this.Analyze symbol compilation addDiagnostic cancellationToken = 
        if symbol.TypeKind = TypeKind.Class && symbol.IsDerivedFromComponent compilation then
            for interfaceSymbol in symbol.AllInterfaces |> Seq.where (fun interfaceSymbol -> interfaceSymbol.ImplementsIComponent compilation) do
                for interfaceMember in interfaceSymbol.GetMembers () do
                    let implementingMember = symbol.FindImplementationForInterfaceMember interfaceMember
                    if implementingMember.ContainingType = symbol then
                        match implementingMember with
                        | :? IMethodSymbol as methodSymbol ->
                            let interfaceMethodSymbol = interfaceMember :?> IMethodSymbol
                            let hasRequiredAttribute = interfaceMethodSymbol.HasAttribute<RequiredAttribute> compilation
                            if hasRequiredAttribute && not methodSymbol.IsExtern then
                                addDiagnostic.Invoke (methodSymbol, methodSymbol.ToDisplayString (), interfaceMember.ToDisplayString ())
                        | :? IPropertySymbol as propertySymbol ->
                            let interfacePropertySymbol = interfaceMember :?> IPropertySymbol
                            let hasRequiredAttribute = interfacePropertySymbol.HasAttribute<RequiredAttribute> compilation
                            if hasRequiredAttribute && not propertySymbol.IsExtern then
                                addDiagnostic.Invoke (propertySymbol, propertySymbol.ToDisplayString (), interfaceMember.ToDisplayString ())
                        | _ -> ()
