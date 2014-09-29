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

namespace SafetySharp.Internal.CSharp.Transformation
//
//open System.Collections.Immutable
//open SafetySharp.Internal.Metamodel
//open SafetySharp.Modeling
//open SafetySharp.Internal.Utilities
//
//module internal ObjectTransformation =
//
//    /// Transforms C# objects to metamodel objects.
//    let Transform (model : Model) (symbolResolver : SymbolResolver) =
//        nullArg model "model"
//        invalidArg (not model.IsMetadataFinalized) "model" "The model metadata has not yet been finalized."
//
//        // We're using the builder pattern to initialize the dictionaries
//        let componentSymbolMapBuilder = ImmutableDictionary.CreateBuilder<IComponent, ComponentSymbol> ()
//        let componentObjectMapBuilder = ImmutableDictionary.CreateBuilder<IComponent, ComponentObject> ()
//
//        // Creates the field objects for the .NET component instance.
//        let transformFields (component' : Component) (componentSymbol : ComponentSymbol) =
//            [
//                for fieldSymbol in componentSymbol.Fields ->
//                    (fieldSymbol, { FieldSymbol = fieldSymbol; InitialValues = component'.GetInitialValuesOfField fieldSymbol.Name })
//            ]
//
//        // Creates the subcomponent objects for the .NET component instance.
//        let rec transformSubcomponents (component' : Component) (componentSymbol : ComponentSymbol) =
//            [
//                for subcomponentSymbol in symbolResolver.Model.Subcomponents.[componentSymbol] ->
//                    (subcomponentSymbol, transformComponent <| component'.GetSubcomponent subcomponentSymbol.Name)
//            ]
//
//        // Creates the objects and mapping information for the .NET component instance.
//        and transformComponent (component' : Component) =
//            let componentSymbol = symbolResolver.ResolveComponent component'
//            let componentObject = {
//                Name = component'.Name
//                ComponentSymbol = componentSymbol
//                Fields = transformFields component' componentSymbol |> Map.ofList
//                Subcomponents = transformSubcomponents component' componentSymbol |> Map.ofList
//                Bindings = Map.empty
//            }
//            
//            componentSymbolMapBuilder.Add (component', componentSymbol)
//            componentObjectMapBuilder.Add (component', componentObject)
//            componentObject 
//
//        // Creates the objects and mapping information for the .NET partition root component instance.
//        let transformPartition (rootComponent : Component) =
//            { RootComponent = transformComponent rootComponent; PartitionSymbol = symbolResolver.ResolvePartition rootComponent }
//
//        // Creates component reference mapping for the component
//        let transformComponentReference (component' : Component) =
//            let componentReference = symbolResolver.ResolveComponentReference component'
//            let componentObject = componentObjectMapBuilder.[component']
//            (componentReference, componentObject)
//
//        // Creates the model object
//        let modelObject = { 
//            ModelSymbol = symbolResolver.ModelSymbol
//            Partitions = model.PartitionRoots |> List.map transformPartition
//            ComponentObjects = model.Components |> List.map transformComponentReference |> Map.ofList
//        }
//
//        // Create and return the object resolver
//        {
//            ComponentSymbolMap = componentSymbolMapBuilder.ToImmutable ()
//            ComponentObjectMap = componentObjectMapBuilder.ToImmutable ()
//            Model = modelObject
//        }