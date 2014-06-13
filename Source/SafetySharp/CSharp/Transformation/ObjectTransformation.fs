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
open SafetySharp.Metamodel
open SafetySharp.Modeling
open SafetySharp.Utilities

/// Represents a mapping between the original .NET objects and the created metamodel symbols and objects.
type ObjectResolver = private {
    ComponentSymbolMap : ImmutableDictionary<Component, ComponentSymbol>
    ComponentObjectMap : ImmutableDictionary<Component, ComponentObject>
    Model : ModelObject
}
    with

    /// Resolves the <see cref="ComponentSymbol"/> corresponding to the given .NET component object.
    member this.ResolveSymbol (componentObject : Component) =
        Requires.NotNull componentObject "componentObject"
        match this.ComponentSymbolMap.TryGetValue componentObject with
        | (result, symbol) when result -> symbol
        | _ -> invalidArg "componentObject" "The given component is unknown."

    /// Resolves the <see cref="ComponentObject"/> corresponding to the given .NET component object.
    member this.ResolveObject (componentObject : Component) =
        Requires.NotNull componentObject "componentObject"
        match this.ComponentObjectMap.TryGetValue componentObject with
        | (result, symbol) when result -> symbol
        | _ -> invalidArg "componentObject" "The given component is unknown."

    /// Gets the model object that contains all of the resolver's component and partition objects.
    member this.ModelObject = this.Model

module ObjectTransformation =

    /// Transforms C# objects to metamodel objects.
    let Transform (model : Model) (symbolResolver : SymbolResolver) =
        Requires.NotNull model "model"
        Requires.ArgumentSatisfies model.IsMetadataFinalized "model" "The model metadata has not yet been finalized."

        // We're using the builder pattern to initialize the dictionaries
        let componentSymbolMapBuilder = ImmutableDictionary.CreateBuilder<Component, ComponentSymbol> ()
        let componentObjectMapBuilder = ImmutableDictionary.CreateBuilder<Component, ComponentObject> ()

        // Create the field objects for the .NET component instance.
        let transformFields (component' : Component) (componentSymbol : ComponentSymbol) =
            [
                for fieldSymbol in componentSymbol.Fields ->
                    (fieldSymbol, { FieldSymbol = fieldSymbol; InitialValues = component'.GetInitialValuesOfField fieldSymbol.Name })
            ]

        // Create the subcomponent objects for the .NET component instance.
        let rec transformSubcomponents (component' : Component) (componentSymbol : ComponentSymbol) =
            [
                for subcomponentSymbol in symbolResolver.Model.Subcomponents.[componentSymbol] ->
                    (subcomponentSymbol, transformComponent <| component'.GetSubcomponent subcomponentSymbol.Name)
            ]

        // Creates the objects and mapping information for the .NET component instance.
        and transformComponent (component' : Component) =
            let componentSymbol = symbolResolver.ResolveComponent component'
            let componentObject = {
                Name = component'.Name
                ComponentSymbol = componentSymbol
                Fields = transformFields component' componentSymbol |> Map.ofList
                Subcomponents = transformSubcomponents component' componentSymbol |> Map.ofList
            }

            componentSymbolMapBuilder.Add (component', componentSymbol)
            componentObjectMapBuilder.Add (component', componentObject)
            componentObject 

        // Creates the objects and mapping information for the .NET partition root component instance.
        let transformPartition (rootComponent : Component) =
            { RootComponent = transformComponent rootComponent } //; PartitionSymbol = (* TODO *) Unchecked.defaultof<PartitionSymbol> }

        // Create the model object
        let model = { 
            //ModelSymbol = (* TODO *) Unchecked.defaultof<ModelSymbol> 
            Partitions = model.PartitionRoots |> List.map transformPartition 
        }

        // Create and return the object resolver
        {
            ComponentSymbolMap = componentSymbolMapBuilder.ToImmutable ()
            ComponentObjectMap = componentObjectMapBuilder.ToImmutable ()
            Model = model
        }