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

open System.Collections.Generic
open System.Collections.Immutable
open System.Runtime.CompilerServices

open SafetySharp.Utilities
open SafetySharp.Metamodel
open SafetySharp.Modeling
open SafetySharp.CSharp.Roslyn

open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax

/// Represents a mapping between the original C# symbols and the created metamodel symbols.
type SymbolResolver = private {
    ComponentList : ComponentSymbol list
    ComponentMap : ImmutableDictionary<ITypeSymbol, ComponentSymbol>
    FieldMap : ImmutableDictionary<IFieldSymbol, FieldSymbol>
    SubComponentMap : ImmutableDictionary<IFieldSymbol, SubcomponentSymbol>
    MethodMap : ImmutableDictionary<IMethodSymbol, MethodSymbol>
    MethodMapBack : ImmutableDictionary<MethodSymbol, IMethodSymbol>
}
    with

    /// Resolves the <see cref="ComponentSymbol"/> corresponding to the given C# component symbol.
    member this.ResolveComponent (componentSymbol : INamedTypeSymbol) =
        Requires.NotNull componentSymbol "componentSymbol"
        match this.ComponentMap.TryGetValue componentSymbol with
        | (result, symbol) when result -> symbol
        | _ -> invalidArg "componentSymbol" "The given C# component symbol is unknown."

    /// Resolves the <see cref="ComponentSymbol"/> corresponding to the given .NET component object.
    member this.ResolveComponent (componentObject : Component) =
        Requires.NotNull componentObject "componentObject"
        let typeName = componentObject.GetType().FullName.Replace("+", ".")
        let assemblyName = componentObject.GetType().Assembly.GetName().Name
        let name = sprintf "%s::%s" assemblyName typeName

        match this.ComponentList |> List.tryFind (fun symbol -> symbol.Name = name) with
        | Some symbol -> symbol
        | None -> invalidArg "componentObject" "The type of the given .NET component instance is unknown."

    /// Resolves the <see cref="FieldSymbol"/> corresponding to the given C# field symbol.
    member this.ResolveField (fieldSymbol : IFieldSymbol) =
        Requires.NotNull fieldSymbol "fieldSymbol"
        match this.FieldMap.TryGetValue fieldSymbol with
        | (result, symbol) when result -> symbol
        | _ -> invalidArg "fieldSymbol" "The given C# field symbol is unknown."

    /// Resolves the <see cref="SubcomponentSymbol"/> corresponding to the given C# subcomponent symbol.
    member this.ResolveSubcomponent (subcomponentSymbol : IFieldSymbol) =
        Requires.NotNull subcomponentSymbol "subcomponentSymbol"
        match this.SubComponentMap.TryGetValue subcomponentSymbol with
        | (result, symbol) when result -> symbol
        | _ -> invalidArg "subcomponentSymbol" "The given C# subcomponent symbol is unknown."

    /// Resolves the <see cref="MethodSymbol"/> corresponding to the given C# method symbol.
    member this.ResolveMethod (methodSymbol : IMethodSymbol) =
        Requires.NotNull methodSymbol "methodSymbol"
        match this.MethodMap.TryGetValue methodSymbol with
        | (result, symbol) when result -> symbol
        | _ -> invalidArg "methodSymbol" "The given C# method symbol is unknown."

    /// Resolves the C# method symbol corresponding to the given metamodel <see cref="MethodSymbol"/>.
    member this.ResolveCSharpMethod (methodSymbol : MethodSymbol) =
        match this.MethodMapBack.TryGetValue methodSymbol with
        | (result, symbol) when result -> symbol
        | _ -> invalidArg "methodSymbol" "The given method symbol is unknown."

    /// Gets a list of all component symbols.
    member this.ComponentSymbols = this.ComponentList

module SymbolTransformation =

    /// Transforms the given component types of the compilation to a symbol map.
    let Transform (compilation : Compilation) =
        Requires.NotNull compilation "compilation"

        // An equality comparer for method symbols that implements reference equality
        let comparer = { 
            new IEqualityComparer<MethodSymbol> with
                member this.Equals (symbol1, symbol2) = 
                    obj.ReferenceEquals(symbol1, symbol2)
                member this.GetHashCode (symbol) =
                    RuntimeHelpers.GetHashCode(symbol)
        }

        // We're using the builder pattern to initialize the dictionaries and the component list
        let componentListBuilder = ImmutableList.CreateBuilder<ComponentSymbol> ()
        let componentMapBuilder = ImmutableDictionary.CreateBuilder<ITypeSymbol, ComponentSymbol> ()
        let fieldMapBuilder = ImmutableDictionary.CreateBuilder<IFieldSymbol, FieldSymbol> ()
        let subComponentMapBuilder = ImmutableDictionary.CreateBuilder<IFieldSymbol, SubcomponentSymbol> ()
        let methodMapBuilder = ImmutableDictionary.CreateBuilder<IMethodSymbol, MethodSymbol> ()
        let methodMapBackBuilder = ImmutableDictionary.CreateBuilder<MethodSymbol, IMethodSymbol> (comparer)

        // Converts a C# type symbol to one of the supported metamodel type symbols
        let toTypeSymbol (csharpSymbol : ITypeSymbol) =
            match csharpSymbol.SpecialType with
            | SpecialType.None -> csharpSymbol.ToDisplayString SymbolDisplayFormat.FullyQualifiedFormat |> sprintf "Type '%s' is not supported." |> invalidOp
            | SpecialType.System_Boolean -> TypeSymbol.Boolean
            | SpecialType.System_Int32 -> TypeSymbol.Integer
            | SpecialType.System_Decimal -> TypeSymbol.Decimal
            | _ -> sprintf "Unsupported C# special type: '%A'." csharpSymbol.SpecialType |> invalidOp

        // Encodes the assembly name and all parent namespaces in the component name to ensure the uniqueness of the name.
        let transformComponentName (csharpComponent : ITypeSymbol) = 
            let assemblyName = csharpComponent.ContainingAssembly.Identity.Name
            let displayFormat = SymbolDisplayFormat (SymbolDisplayGlobalNamespaceStyle.Omitted, SymbolDisplayTypeQualificationStyle.NameAndContainingTypesAndNamespaces)
            let componentName = csharpComponent.ToDisplayString displayFormat
            sprintf "%s::%s" assemblyName componentName

        // Creates the symbols and optional mapping information for the Update method of the component.
        let transformUpdateMethod (csharpComponent : ITypeSymbol) =
            let updateMethods = csharpComponent.GetMembers().OfType<IMethodSymbol>() |> Seq.filter (fun method' -> method'.IsUpdateMethod compilation)
            let updateMethodCount = updateMethods |> Seq.length
            let methodSymbol = { Name = "Update"; ReturnType = None; Parameters = [] }

            if updateMethodCount > 1 then 
                csharpComponent.ToDisplayString () |> sprintf "Component of type '%A' defines more than one Update() method." |> invalidOp
            else if updateMethodCount = 1 then
                let updateMethod = updateMethods |> Seq.head
                methodMapBuilder.Add (updateMethod, methodSymbol)
                methodMapBackBuilder.Add (methodSymbol, updateMethod)
            methodSymbol

        // Create the symbols and mapping information for all methods of the component. We'll also build up a 
        // dictionary that allows us to retrieve the original C# method symbol again.
        let transformMethods (csharpComponent : ITypeSymbol) =
            let transformReturnType (returnType : ITypeSymbol) =
                if returnType.SpecialType = SpecialType.System_Void then 
                    None 
                else 
                    Some <| toTypeSymbol returnType

            let transformParameter (parameter : IParameterSymbol) =
                { ParameterSymbol.Name = parameter.Name; Type = toTypeSymbol parameter.Type }

            let methods = 
                csharpComponent.GetMembers().OfType<IMethodSymbol>() 
                |> Seq.filter (fun method' -> not <| method'.IsUpdateMethod compilation && method'.MethodKind = MethodKind.Ordinary)

            [
                for csharpMethod in methods ->
                    let methodSymbol = { 
                        Name = csharpMethod.Name
                        ReturnType = transformReturnType csharpMethod.ReturnType
                        Parameters = [ for parameter in csharpMethod.Parameters -> transformParameter parameter ]
                    }
                    methodMapBuilder.Add (csharpMethod, methodSymbol)
                    methodMapBackBuilder.Add (methodSymbol, csharpMethod)
                    methodSymbol
            ]

        // Creates the symbols and mapping information for all fields of the component.
        let transformFields (csharpComponent : ITypeSymbol) =
            let fields = csharpComponent.GetMembers().OfType<IFieldSymbol>() |> Seq.filter (fun field -> not <| field.IsSubcomponentField compilation)
            [
                for csharpField in fields -> 
                    let fieldSymbol = { FieldSymbol.Name = csharpField.Name; Type = toTypeSymbol csharpField.Type }
                    fieldMapBuilder.Add (csharpField, fieldSymbol)
                    fieldSymbol
            ]

        // Creates the symbols and mapping information for all subcomponents of the component.
        let transformSubcomponents (csharpComponent : ITypeSymbol) =
            let fields = csharpComponent.GetMembers().OfType<IFieldSymbol>() |> Seq.filter (fun field -> field.IsSubcomponentField compilation)
            [
                for csharpField in fields -> 
                    let subComponentSymbol = { SubcomponentSymbol.Name = csharpField.Name }
                    subComponentMapBuilder.Add (csharpField, subComponentSymbol)
                    subComponentSymbol
            ]

        // Creates the symbols and mapping information for a component with the given type.
        let transformComponent (csharpComponent : ITypeSymbol) =
            let componentSymbol = {
                Name = transformComponentName csharpComponent
                UpdateMethod = transformUpdateMethod csharpComponent
                Methods = transformMethods csharpComponent
                Fields = transformFields csharpComponent
                Subcomponents = transformSubcomponents csharpComponent
            }

            componentListBuilder.Add componentSymbol
            componentMapBuilder.Add (csharpComponent, componentSymbol)

        // Create the symbols for all components
        let csharpComponents = compilation.GetTypeSymbols () |> Seq.filter (fun csharpComponent -> csharpComponent.IsDerivedFromComponent compilation)
        csharpComponents |> Seq.iter transformComponent

        // Create and return the symbol resolver
        {
            ComponentMap = componentMapBuilder.ToImmutable ()
            ComponentList = componentListBuilder |> List.ofSeq
            FieldMap = fieldMapBuilder.ToImmutable ()
            SubComponentMap = subComponentMapBuilder.ToImmutable ()
            MethodMap = methodMapBuilder.ToImmutable ()
            MethodMapBack = methodMapBackBuilder.ToImmutable ()
        }