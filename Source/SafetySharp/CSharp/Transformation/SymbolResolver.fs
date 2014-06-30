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

namespace SafetySharp.CSharp.Transformation

open System.Collections.Immutable
open SafetySharp.Metamodel
open SafetySharp.Modeling
open SafetySharp.Utilities
open Microsoft.CodeAnalysis

/// Represents a mapping between the original C# symbols and the created metamodel symbols.
type internal SymbolResolver = private {
    Model : ModelSymbol
    ComponentMap : ImmutableDictionary<ITypeSymbol, ComponentSymbol>
    ComponentNameMap : Map<string, ComponentSymbol>
    FieldMap : ImmutableDictionary<IFieldSymbol, FieldSymbol>
    SubcomponentMap : ImmutableDictionary<IFieldSymbol, ComponentReferenceSymbol>
    ParameterMap : ImmutableDictionary<IParameterSymbol, ParameterSymbol>
    LocalMap : ImmutableDictionary<ILocalSymbol, LocalSymbol>
    MethodMap : ImmutableDictionary<IMethodSymbol, MethodSymbol>
    MethodCSharpMap : ImmutableDictionary<MethodSymbol, IMethodSymbol>
    IComponentTypeSymbol : ComponentSymbol
    ComponentBaseTypeSymbol : ComponentSymbol
}
    with

    /// Resolves the <see cref="ComponentSymbol"/> corresponding to the given C# component symbol.
    member this.ResolveComponent (componentSymbol : INamedTypeSymbol) =
        nullArg componentSymbol "componentSymbol"
        let (result, symbol) = this.ComponentMap.TryGetValue componentSymbol
        invalidArg (not result) "componentSymbol" "The given C# component symbol '%s' is unknown." <| componentSymbol.ToDisplayString ()
        symbol

    /// Resolves the <see cref="ComponentSymbol"/> corresponding to the given .NET component object.
    member this.ResolveComponent (componentObject : IComponent) =
        nullArg componentObject "componentObject"
        let typeName = componentObject.GetType().FullName.Replace("+", ".")
        let assemblyName = componentObject.GetType().Assembly.GetName().Name
        let name = sprintf "%s::%s" assemblyName typeName

        let symbol = this.ComponentNameMap |> Map.tryFind name
        invalidArg symbol.IsNone "componentObject" "Unknown component type '%s'." <| componentObject.GetType().FullName
        symbol.Value

    /// Resolves the model's <see cref="ComponentReferenceSymbol" /> corresponding to the given C# component object.
    member this.ResolveComponentReference (componentObject : IComponent) =
        nullArg componentObject "componentObject"
        invalidCall (List.isEmpty this.Model.ComponentObjects) "No component object symbols have been created yet for the model."
        let symbol = this.Model.ComponentObjects |> List.tryFind (fun symbol -> symbol.Name = componentObject.Name)
        invalidArg symbol.IsNone "componentObject" "Unknown component type '%s'." <| componentObject.GetType().FullName
        symbol.Value

    /// Resolves the <see cref="PartitionSymbol" /> corresponding to the given C# component object.
    member this.ResolvePartition (componentObject : IComponent) =
        nullArg componentObject "componentObject"
        invalidCall (List.isEmpty this.Model.Partitions) "No partition symbols have been created yet for the model."
        let symbol = this.Model.Partitions |> List.tryFind (fun symbol -> symbol.Name = componentObject.Name)
        invalidArg symbol.IsNone "componentObject" "Unknown partition '%s'." <| componentObject.Name
        symbol.Value

    /// Resolves the <see cref="FieldSymbol"/> corresponding to the given C# field symbol.
    member this.ResolveField (fieldSymbol : IFieldSymbol) =
        nullArg fieldSymbol "fieldSymbol"
        let (result, symbol) = this.FieldMap.TryGetValue fieldSymbol
        invalidArg (not result) "fieldSymbol" "The given C# field symbol '%s' is unknown." <| fieldSymbol.ToDisplayString ()
        symbol

    /// Resolves the <see cref="ComponentReferenceSymbol"/> corresponding to the given C# subcomponent symbol.
    member this.ResolveSubcomponent (subcomponentSymbol : IFieldSymbol) =
        nullArg subcomponentSymbol "subcomponentSymbol"
        let (result, symbol) = this.SubcomponentMap.TryGetValue subcomponentSymbol
        invalidArg (not result) "subcomponentSymbol" "The given C# subcomponent symbol '%s' is unknown." <| subcomponentSymbol.ToDisplayString ()
        symbol

    /// Resolves the <see cref="ParameterSymbol"/> corresponding to the given C# parameter symbol.
    member this.ResolveParameter (parameterSymbol : IParameterSymbol) =
        nullArg parameterSymbol "parameterSymbol"
        let (result, symbol) = this.ParameterMap.TryGetValue parameterSymbol
        invalidArg (not result) "parameterSymbol" "The given C# parameter symbol '%s' is unknown." <| parameterSymbol.ToDisplayString ()
        symbol

    /// Resolves the <see cref="LocalSymbol"/> corresponding to the given C# local symbol.
    member this.ResolveLocal (localSymbol : ILocalSymbol) =
        nullArg localSymbol "localSymbol"
        let (result, symbol) = this.LocalMap.TryGetValue localSymbol
        invalidArg (not result) "localSymbol" "The given C# local symbol '%s' is unknown." <| localSymbol.ToDisplayString ()
        symbol

    /// Resolves the <see cref="MethodSymbol"/> corresponding to the given C# method symbol.
    member this.ResolveMethod (methodSymbol : IMethodSymbol) =
        nullArg methodSymbol "methodSymbol"
        let (result, symbol) = this.MethodMap.TryGetValue methodSymbol
        invalidArg (not result) "methodSymbol" "The given C# method symbol '%s' is unknown." <| methodSymbol.ToDisplayString ()
        symbol

    /// Resolves the C# method symbol corresponding to the given metamodel <see cref="MethodSymbol"/>.
    member this.ResolveCSharpMethod (methodSymbol : MethodSymbol) =
        let (result, symbol) = this.MethodCSharpMap.TryGetValue methodSymbol
        invalidArg (not result) "methodSymbol" "The given method symbol '%s' is unknown." methodSymbol.Name
        symbol

    /// Gets the model symbol that contains all of the symbols of the symbol resolver.
    member this.ModelSymbol = this.Model

    /// Gets all component symbols contained in the symbol resolver.
    member this.ComponentSymbols = this.Model.ComponentSymbols

    /// Gets the symbol representing the <see cref="SafetySharp.Modeling.IComponent"/> interface.
    member this.ComponentInterfaceSymbol = this.IComponentTypeSymbol

    /// Gets the symbol representing the <see cref="SafetySharp.Modeling.Component"/> class.
    member this.ComponentBaseSymbol = this.ComponentBaseTypeSymbol