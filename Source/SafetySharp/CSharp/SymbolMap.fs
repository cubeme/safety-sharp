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

open System.Collections.Immutable

open SafetySharp.Utilities
open SafetySharp.Metamodel
open SafetySharp.CSharp.Roslyn

open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax

/// Constructs symbols for the given component types and creates a mapping between the original C# symbols and the
/// created metamodel symbols.
type SymbolMap (compilation : CSharpCompilation, componentTypes : string list) =
    do Requires.NotNull compilation "compilation"

    // We're using the builder pattern to initialize the dictionaries
    let componentMapBuilder = ImmutableDictionary.CreateBuilder<INamedTypeSymbol, ComponentSymbol> ()
    let fieldMapBuilder = ImmutableDictionary.CreateBuilder<IFieldSymbol, FieldSymbol> ()
    let subComponentMapBuilder = ImmutableDictionary.CreateBuilder<IFieldSymbol, SubcomponentSymbol> ()
    let methodMapBuilder = ImmutableDictionary.CreateBuilder<IMethodSymbol, MethodSymbol> ()
    let methodMapBackBuilder = ImmutableDictionary.CreateBuilder<MethodSymbol, IMethodSymbol> ()

    // Converts a C# type symbol to one of the supported metamodel type symbols
    let toTypeSymbol (csharpSymbol : ITypeSymbol) =
        match csharpSymbol.SpecialType with
        | SpecialType.None -> sprintf "Type '%A' is not yet supported." csharpSymbol.SpecialType |> invalidOp
        | SpecialType.System_Boolean -> TypeSymbol.Boolean
        | SpecialType.System_Int32 -> TypeSymbol.Integer
        | SpecialType.System_Decimal -> TypeSymbol.Decimal
        | _ -> sprintf "Unsupported C# type: '%A'." csharpSymbol.SpecialType |> invalidOp

    // Create the symbols for all components
    do for syntaxTree in compilation.SyntaxTrees do
        let semanticModel = compilation.GetSemanticModel syntaxTree
        for componentType in componentTypes do
            let csharpComponent = semanticModel.GetTypeSymbol componentType
            let fields = csharpComponent.GetMembers().OfType<IFieldSymbol>()
            let methods = csharpComponent.GetMembers().OfType<IMethodSymbol>()

            let componentSymbol = {
                // The name of a component corresponds to the fully qualified name of the C# class the symbol was generated from.
                Name = csharpComponent.ToDisplayString SymbolDisplayFormat.FullyQualifiedFormat

                // Creates the symbols and optional mapping information for the Update method of the component.
                UpdateMethod = 
                    let updateMethods = methods |> Seq.filter (fun method' -> method'.IsUpdateMethod semanticModel)
                    let updateMethodCount = updateMethods |> Seq.length
                    let methodSymbol = { Name = "Update"; ReturnType = None; Parameters = [] }

                    if updateMethodCount > 1 then 
                        sprintf "Component of type '%A' defines more than one Update() method." componentType |> invalidOp
                    else if updateMethodCount = 1 then
                        let updateMethod = updateMethods |> Seq.head
                        methodMapBuilder.Add (updateMethod, methodSymbol)
                        methodMapBackBuilder.Add (methodSymbol, updateMethod)
                    methodSymbol

                // Create the symbols and mapping information for all methods of the component. We'll also build up a 
                // dictionary that allows us to retrieve the original C# method symbol again.
                Methods = 
                    [
                        let methods = methods |> Seq.filter (fun method' -> not <| method'.IsUpdateMethod semanticModel)
                        for csharpMethod in methods ->
                            let methodSymbol = { Name = csharpMethod.Name; ReturnType = None; Parameters = []}
                            methodMapBuilder.Add (csharpMethod, methodSymbol)
                            methodMapBackBuilder.Add (methodSymbol, csharpMethod)
                            methodSymbol
                    ]

                // Creates the symbols and mapping information for all fields of the component.
                Fields = 
                    [
                        let fields = fields |> Seq.filter (fun field -> not <| field.IsSubcomponentField semanticModel)
                        for csharpField in fields -> 
                            let fieldSymbol = { FieldSymbol.Name = csharpField.Name; Type = toTypeSymbol csharpField.Type }
                            fieldMapBuilder.Add (csharpField, fieldSymbol)
                            fieldSymbol
                    ]

                // Creates the symbols and mapping information for all subcomponents of the component.
                Subcomponents = 
                    [
                        let fields = fields |> Seq.filter (fun field -> field.IsSubcomponentField semanticModel)
                        for csharpField in fields -> 
                            let subComponentSymbol = { SubcomponentSymbol.Name = csharpField.Name }
                            subComponentMapBuilder.Add (csharpField, subComponentSymbol)
                            subComponentSymbol
                    ]
            }

            componentMapBuilder.Add (csharpComponent, componentSymbol)

    // Create the dictionaries that we'll later use to resolve C# symbols to metamodel symbols.
    let componentMap = componentMapBuilder.ToImmutable ()
    let fieldMap = fieldMapBuilder.ToImmutable ()
    let subComponentMap = subComponentMapBuilder.ToImmutable ()
    let methodMap = methodMapBuilder.ToImmutable ()
    let methodMapBack = methodMapBackBuilder.ToImmutable ()

    /// Resolves the <see cref="ComponentSymbol"/> corresponding to the given C# component symbol.
    member this.Resolve (componentSymbol : INamedTypeSymbol) =
        Requires.NotNull componentSymbol "componentSymbol"
        Requires.That (componentMap.ContainsKey componentSymbol) "The given C# component symbol is unknown."
        componentMap.[componentSymbol]

    /// Resolves the <see cref="FieldSymbol"/> corresponding to the given C# field symbol.
    member this.ResolveField (fieldSymbol : IFieldSymbol) =
        Requires.NotNull fieldSymbol "fieldSymbol"
        Requires.That (fieldMap.ContainsKey fieldSymbol) "The given C# field symbol is unknown."
        fieldMap.[fieldSymbol]

    /// Resolves the <see cref="SubcomponentSymbol"/> corresponding to the given C# subcomponent symbol.
    member this.ResolveSubcomponent (subcomponentSymbol : IFieldSymbol) =
        Requires.NotNull subcomponentSymbol "subcomponentSymbol"
        Requires.That (fieldMap.ContainsKey subcomponentSymbol) "The given C# subcomponent symbol is unknown."
        subComponentMap.[subcomponentSymbol]

    /// Resolves the <see cref="MethodSymbol"/> corresponding to the given C# method symbol.
    member this.Resolve (methodSymbol : IMethodSymbol) =
        Requires.NotNull methodSymbol "methodSymbol"
        Requires.That (methodMap.ContainsKey methodSymbol) "The given C# method symbol is unknown."
        methodMap.[methodSymbol]

    /// Resolves the C# method symbol corresponding to the given metamodel <see cref="MethodSymbol"/>.
    member this.Resolve (methodSymbol : MethodSymbol) =
        Requires.That (methodMapBack.ContainsKey methodSymbol) "The given method symbol is unknown."
        methodMapBack.[methodSymbol]

    /// Gets a list of all component symbols.
    member this.Components = componentMap.Values |> List.ofSeq