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
//open System.Collections.Generic
//open System.Collections.Immutable
//open System.Runtime.CompilerServices
//open SafetySharp.Internal.Utilities
//open SafetySharp.Internal.Metamodel
//open SafetySharp.Modeling
//open SafetySharp.Internal.CSharp.Roslyn
//open Microsoft.CodeAnalysis
//open Microsoft.CodeAnalysis.CSharp
//open Microsoft.CodeAnalysis.CSharp.Syntax
//
//module internal SymbolTransformation =
//
//    /// Transforms the component declarations within the given compilation to a symbol resolver.
//    let TransformComponentSymbols (compilation : Compilation) =
//        nullArg compilation "compilation"
//
//        // An equality comparer for method symbols that implements reference equality
//        let comparer = { 
//            new IEqualityComparer<MethodSymbol> with
//                member this.Equals (symbol1, symbol2) = 
//                    obj.ReferenceEquals (symbol1, symbol2)
//                member this.GetHashCode symbol =
//                    RuntimeHelpers.GetHashCode symbol
//        }
//
//        // We're using the builder pattern to initialize the dictionaries and the component list
//        let componentListBuilder = ImmutableList.CreateBuilder<ComponentSymbol> ()
//        let componentMapBuilder = ImmutableDictionary.CreateBuilder<ITypeSymbol, ComponentSymbol> ()
//        let componentNameMapBuilder = ImmutableDictionary.CreateBuilder<string, ComponentSymbol> ()
//        let fieldMapBuilder = ImmutableDictionary.CreateBuilder<IFieldSymbol, FieldSymbol> ()
//        let subcomponentMapBuilder = ImmutableDictionary.CreateBuilder<IFieldSymbol, ComponentReferenceSymbol> ()
//        let parameterMapBuilder = ImmutableDictionary.CreateBuilder<IParameterSymbol, ParameterSymbol> ()
//        let localMapBuilder = ImmutableDictionary.CreateBuilder<ILocalSymbol, LocalSymbol> ()
//        let methodMapBuilder = ImmutableDictionary.CreateBuilder<IMethodSymbol, MethodSymbol> ()
//        let methodCSharpMapBuilder = ImmutableDictionary.CreateBuilder<MethodSymbol, IMethodSymbol> comparer
//
//        // Maps a component by its name
//        let mapComponentByName (component' : ComponentSymbol) =
//            match componentNameMapBuilder.TryGetValue component'.Name with
//            | (true, otherComponent) ->
//                let getAssemblyName component' =
//                    (componentMapBuilder |> Seq.find (fun pair -> pair.Value = component')).Key.ContainingAssembly.Identity.ToString ()
//                let assembly1 = getAssemblyName component'
//                let assembly2 = getAssemblyName otherComponent
//                invalidOp "Found two components with same name '%s' defined in assembly '%s' and '%s'." component'.Name assembly1 assembly2
//            | (false, _) ->
//                componentNameMapBuilder.Add (component'.Name, component')
//
//        // Instantiate the component symbols for the Component base class and the IComponent interface
//        let createComponentSymbol name csharpSymbol = 
//            let symbol = { 
//                Name = name
//                UpdateMethod = None
//                ProvidedPorts = []
//                RequiredPorts = [] 
//                Fields = [] 
//            }
//            componentMapBuilder.Add (csharpSymbol, symbol)
//            mapComponentByName symbol
//            symbol
//
//        let componentBaseSymbol = createComponentSymbol "Component" (compilation.GetComponentClassSymbol ())
//        let componentInterfaceSymbol = createComponentSymbol "IComponent" (compilation.GetComponentInterfaceSymbol ())
//
//        // Converts a C# type symbol to one of the supported metamodel type symbols
//        let toTypeSymbol (csharpSymbol : ITypeSymbol) =
//            match csharpSymbol.SpecialType with
//            | SpecialType.None -> csharpSymbol.ToDisplayString SymbolDisplayFormat.FullyQualifiedFormat |> invalidOp "Type '%s' is not supported."
//            | SpecialType.System_Boolean -> TypeSymbol.Boolean
//            | SpecialType.System_Int32 -> TypeSymbol.Integer
//            | SpecialType.System_Decimal -> TypeSymbol.Decimal
//            | _ -> invalidOp "Unsupported C# special type: '%A'." csharpSymbol.SpecialType
//
//        // Encodes the assembly name and all parent namespaces in the component name to ensure the uniqueness of the name.
//        let transformComponentName (csharpComponent : ITypeSymbol) = 
//            let displayFormat = SymbolDisplayFormat (SymbolDisplayGlobalNamespaceStyle.Omitted, SymbolDisplayTypeQualificationStyle.NameAndContainingTypesAndNamespaces)
//            let componentName = csharpComponent.ToDisplayString displayFormat
//            componentName
//
//        // Creates the symbols and mapping information for the local variables of the given method.
//        let transformLocals (methodSymbol : IMethodSymbol) =
//            let transformLocal (local : ILocalSymbol) =
//                let localSymbol = { LocalSymbol.Name = local.Name; Type = toTypeSymbol local.Type }
//                localMapBuilder.Add (local, localSymbol)
//                localSymbol
//
//            let methodDeclaration = methodSymbol.GetMethodDeclaration ()
//            let semanticModel = methodSymbol.GetSemanticModel compilation
//            methodDeclaration.Descendants<VariableDeclaratorSyntax> ()
//            |> Seq.map (fun declarator -> semanticModel.GetDeclaredSymbol declarator :?> ILocalSymbol)
//            |> Seq.map transformLocal
//            |> List.ofSeq
//
//        // Creates the mapping information for the Update method of the component.
//        let rec transformUpdateMethod (csharpComponent : ITypeSymbol) =
//            let updateMethods = 
//                csharpComponent.GetMembers().OfType<IMethodSymbol>() 
//                |> Seq.filter (fun method' -> method'.IsUpdateMethod compilation)
//                |> List.ofSeq
//
//            match updateMethods with
//            | updateMethod :: [] ->
//                let methodSymbol = { Name = updateMethod.Name; ReturnType = None; Parameters = []; Locals = transformLocals updateMethod }
//                methodMapBuilder.Add (updateMethod, methodSymbol)
//                methodCSharpMapBuilder.Add (methodSymbol, updateMethod)
//                Some methodSymbol
//            | [] when csharpComponent.BaseType <> null ->
//                transformUpdateMethod csharpComponent.BaseType
//            | [] ->
//                None
//            | _ ->
//                csharpComponent.ToDisplayString () |> invalidOp "Component of type '%A' defines more than one Update() method."
//
//        // Creates the symbols and mapping information for all methods of the component. We'll also build up a 
//        // dictionary that allows us to retrieve the original C# method symbol again.
//        let transformMethods (csharpComponent : ITypeSymbol) methodTypeSelector portConstructor =
//            let transformReturnType (returnType : ITypeSymbol) =
//                if returnType.SpecialType = SpecialType.System_Void then 
//                    None 
//                else 
//                    Some <| toTypeSymbol returnType
//
//            let transformParameter (parameter : IParameterSymbol) =
//                let parameterSymbol = { ParameterSymbol.Name = parameter.Name; Type = toTypeSymbol parameter.Type }
//                parameterMapBuilder.Add (parameter, parameterSymbol)
//                parameterSymbol
//
//            let methods = 
//                csharpComponent.GetMembers().OfType<IMethodSymbol>() 
//                |> Seq.filter (fun method' -> not <| method'.IsUpdateMethod compilation && method'.MethodKind = MethodKind.Ordinary)
//                |> Seq.filter methodTypeSelector
//
//            methods |> Seq.map (fun csharpMethod ->
//                let methodSymbol = { 
//                    Name = csharpMethod.Name
//                    ReturnType = transformReturnType csharpMethod.ReturnType
//                    Parameters = csharpMethod.Parameters |> Seq.map transformParameter |> List.ofSeq
//                    Locals = transformLocals csharpMethod
//                }
//                methodMapBuilder.Add (csharpMethod, methodSymbol)
//                methodCSharpMapBuilder.Add (methodSymbol, csharpMethod)
//                portConstructor methodSymbol
//            ) |> List.ofSeq
//
//        // Creates the symbols and mapping information for all fields of the component.
//        let transformFields (csharpComponent : ITypeSymbol) =
//            let fields = csharpComponent.GetMembers().OfType<IFieldSymbol>() |> Seq.filter (fun field -> not <| field.IsSubcomponentField compilation)
//            [
//                for csharpField in fields -> 
//                    let fieldSymbol = { FieldSymbol.Name = csharpField.Name; Type = toTypeSymbol csharpField.Type }
//                    fieldMapBuilder.Add (csharpField, fieldSymbol)
//                    fieldSymbol
//            ]
//
//        // Creates the symbols and mapping information for a component with the given type.
//        let transformComponent (csharpComponent : ITypeSymbol) =
//            let isExtern (methodSymbol : IMethodSymbol) = methodSymbol.IsExtern
//            let componentSymbol = {
//                Name = transformComponentName csharpComponent
//                UpdateMethod = transformUpdateMethod csharpComponent
//                ProvidedPorts = transformMethods csharpComponent (not << isExtern) ProvidedPort
//                RequiredPorts = transformMethods csharpComponent isExtern RequiredPort
//                Fields = transformFields csharpComponent
//            }
//            componentListBuilder.Add componentSymbol
//            componentMapBuilder.Add (csharpComponent, componentSymbol)
//            mapComponentByName componentSymbol
//
//        // Create the symbols for all components
//        let csharpComponents = 
//            compilation.GetTypeSymbols () 
//            |> Seq.filter (fun csharpComponent -> csharpComponent.IsDerivedFromComponent compilation)
//            |> Array.ofSeq
//        csharpComponents |> Array.iter transformComponent
//
//        // Create the first (incomplete) version of the symbol resolver
//        let symbolResolver = {
//            Model = { Partitions = []; ComponentSymbols = componentListBuilder |> List.ofSeq; Subcomponents = Map.empty; ComponentObjects = [] }
//            ComponentMap = componentMapBuilder.ToImmutable ()
//            ComponentNameMap = componentNameMapBuilder.ToImmutable ()
//            FieldMap = fieldMapBuilder.ToImmutable ()
//            SubcomponentMap = ImmutableDictionary<IFieldSymbol, ComponentReferenceSymbol>.Empty
//            ParameterMap = parameterMapBuilder.ToImmutable ()
//            LocalMap = localMapBuilder.ToImmutable ()
//            MethodMap = methodMapBuilder.ToImmutable ()
//            MethodCSharpMap = methodCSharpMapBuilder.ToImmutable ()
//            ComponentBaseTypeSymbol = componentBaseSymbol
//            IComponentTypeSymbol = componentInterfaceSymbol
//        }
//
//        // Creates the symbols and mapping information for all subcomponents of the component.
//        let transformSubcomponents (csharpComponent : ITypeSymbol) =
//            let fields = csharpComponent.GetMembers().OfType<IFieldSymbol>() |> Seq.filter (fun field -> field.IsSubcomponentField compilation)
//            let subcomponents = fields |> Seq.map (fun csharpField ->
//                let componentSymbol = symbolResolver.ResolveComponent (csharpField.Type :?> INamedTypeSymbol)
//                let subComponentSymbol = { ComponentReferenceSymbol.Name = csharpField.Name; ComponentSymbol = componentSymbol }
//                subcomponentMapBuilder.Add (csharpField, subComponentSymbol)
//                subComponentSymbol
//            )
//            (symbolResolver.ResolveComponent (csharpComponent :?> INamedTypeSymbol), subcomponents |> List.ofSeq)
//
//        // Create and return the model symbol and the final version of the symbol resolver
//        let modelSymbol = { symbolResolver.Model with Subcomponents = csharpComponents |> Array.map transformSubcomponents |> Map.ofArray }
//        { symbolResolver with Model = modelSymbol; SubcomponentMap = subcomponentMapBuilder.ToImmutable () }
//
//    /// Transforms the model, adding it to the given symbol resolver.
//    let TransformModelSymbol (symbolResolver : SymbolResolver) (model : Model) =
//        nullArg model "model"
//        invalidArg (not model.IsMetadataFinalized) "model" "The model metadata has not yet been finalized."
//
//        /// Creates the symbols for the partition defined by the given root component.
//        let transformPartition (rootComponent : Component) =
//            { Name = rootComponent.Name; RootComponent = symbolResolver.ResolveComponent rootComponent }
//
//        /// Creates the symbols for the component references of the model's component objects.
//        let transformComponentObjects (component' : Component) = 
//            { ComponentReferenceSymbol.Name = component'.Name; ComponentSymbol = symbolResolver.ResolveComponent component' }
//
//        // Create and return the model symbol and the final version of the symbol resolver
//        let modelSymbol = { 
//            symbolResolver.Model with 
//                Partitions = model.PartitionRoots |> List.map transformPartition
//                ComponentObjects = model.Components |> List.map transformComponentObjects
//        }
//
//        // Return the updated symbol resolver
//        { symbolResolver with Model = modelSymbol }
//
//    /// Transforms the given compilation and model to a symbol resolver.
//    let Transform (compilation : Compilation) (model : Model) =
//        let symbolResolver = TransformComponentSymbols compilation
//        TransformModelSymbol symbolResolver model