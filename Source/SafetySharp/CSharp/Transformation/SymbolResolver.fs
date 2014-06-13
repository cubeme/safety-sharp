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
open SafetySharp.Utilities
open SafetySharp.Metamodel
open SafetySharp.Modeling
open Microsoft.CodeAnalysis

/// Represents a mapping between the original C# symbols and the created metamodel symbols.
type SymbolResolver = private {
    Model : ModelSymbol
    ComponentMap : ImmutableDictionary<ITypeSymbol, ComponentSymbol>
    ComponentNameMap : Map<string, ComponentSymbol>
    FieldMap : ImmutableDictionary<IFieldSymbol, FieldSymbol>
    SubcomponentMap : ImmutableDictionary<IFieldSymbol, SubcomponentSymbol>
    MethodMap : ImmutableDictionary<IMethodSymbol, MethodSymbol>
    MethodCSharpMap : ImmutableDictionary<MethodSymbol, IMethodSymbol>
    IComponentTypeSymbol : ComponentSymbol
    ComponentBaseTypeSymbol : ComponentSymbol
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

        match this.ComponentNameMap |> Map.tryFind name with
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
        match this.SubcomponentMap.TryGetValue subcomponentSymbol with
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
        match this.MethodCSharpMap.TryGetValue methodSymbol with
        | (result, symbol) when result -> symbol
        | _ -> invalidArg "methodSymbol" "The given method symbol is unknown."

    /// Gets the model symbol that contains all of the symbols of the symbol resolver.
    member this.ModelSymbol = this.Model

    /// Gets all component symbols contained in the symbol resolver.
    member this.ComponentSymbols = this.Model.ComponentSymbols

    /// Gets the symbol representing the <see cref="SafetySharp.Modeling.IComponent"/> interface.
    member this.ComponentInterfaceSymbol = this.IComponentTypeSymbol

    /// Gets the symbol representing the <see cref="SafetySharp.Modeling.Component"/> class.
    member this.ComponentBaseSymbol = this.ComponentBaseTypeSymbol