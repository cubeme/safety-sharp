// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
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

namespace SafetySharp

open System
open System.Collections.Generic
open System.Collections.Immutable
open System.Reflection
open SafetySharp
open SafetySharp.Utilities
open SafetySharp.CompilerServices
open Mono.Cecil

/// Provides helper functions for working with the reflection APIs.
module internal Reflection =

    /// Gets the given type's method that implements the given interface method.
    let private getImplementingMethod (typeInfo : Type) (interfaceMethod : MethodInfo) =
        let map = typeInfo.GetInterfaceMap interfaceMethod.DeclaringType
        let index = map.InterfaceMethods |> Array.findIndex ((=) interfaceMethod)
        map.TargetMethods.[index]

    /// Gets the given type's method that overrides the given non-interface method. If the type does not override the method,
    /// the given method is returned.
    let rec private getOverridingMethod (typeInfo : Type) (baseMethod : MethodInfo) =
        let methods = typeInfo.GetMethods (BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.DeclaredOnly)
        match methods |> Array.tryFind (fun m -> m = baseMethod || m.GetBaseDefinition () = baseMethod) with
        | Some m -> m
        | None ->
            if typeInfo.BaseType <> null then getOverridingMethod typeInfo.BaseType baseMethod
            else baseMethod

    /// Gets the most derived implementation of the given virtual or interface method of the given type.
    let getMostDerivedMethod (typeInfo : Type) (baseMethod : MethodInfo) =
        // Resolve the method that implements the interface method
        let targetMethod = if baseMethod.DeclaringType.IsInterface then getImplementingMethod typeInfo baseMethod else baseMethod

        // Resolve the method that overrides the target method; this is also required for implicit, 
        // virtual interface method implementations
        getOverridingMethod typeInfo targetMethod

    /// Provides extension methods for type definitions.
    type private TypeDefinition with
        /// Gets all methods declared by the type, except for constructors.
        member this.GetMethods () = this.Methods |> Seq.filter (fun m -> not m.IsConstructor)

    /// Renames members of types, giving them unique names.
    module Renaming =
        [<Literal>]
        let InheritanceToken = '$'

        [<Literal>]
        let OverloadToken = '@'

        [<Literal>]
        let VarToken = '!'

        /// Computes the inheritance level of a component, i.e., the distance to the System.Object base class
        /// in the inheritance chain.
        let rec getInheritanceLevel (t : TypeDefinition) =
            if t.FullName = typeof<obj>.FullName || t.BaseType = null then 0
            else (getInheritanceLevel (t.BaseType.Resolve ())) + 1

        /// Returns a unique name for the given field name and inheritance level.
        let makeUniqueFieldName fieldName inheritanceLevel =
            sprintf "%s%s" fieldName (String (InheritanceToken, inheritanceLevel))

        /// Returns a unique name for the given method name, inheritance level and overload index.
        let makeUniqueMethodName methodName inheritanceLevel overloadIndex =
            sprintf "%s%s%s" methodName (String (InheritanceToken, inheritanceLevel)) (String (OverloadToken, overloadIndex))

        /// Gets a unique name for the given field within the declaring type's inheritance hierarchy.
        let getUniqueFieldName (f : FieldReference) =
            let f = f.Resolve ()
            let level = getInheritanceLevel f.DeclaringType
            makeUniqueFieldName f.Name level

        /// Gets a unique name for the given method within the declaring type's inheritance hierarchy. Overloaded methods
        /// are also assigned unique names.
        let getUniqueMethodName (m : MethodDefinition) =
            let level = getInheritanceLevel m.DeclaringType
            let index = 
                m.DeclaringType.GetMethods() 
                |> Seq.filter (fun m' -> m'.Name = m.Name)
                |> Seq.toList
                |> List.findIndex ((=) m)

            makeUniqueMethodName m.Name level index

    /// Provides assembly metadata, automatically looking for and using embedded S# assemblies.
    [<AllowNullLiteral>]
    type internal MetadataProvider (types : System.Type list) as this =
        inherit DefaultAssemblyResolver ()

        /// The assemblies that have been loaded by the metadata provider.
        let loadedAssemblies = Dictionary<string, AssemblyDefinition> ()
        let typeReferences = Dictionary<System.Type, TypeReference> ()

        /// Loads the assembly with the given name.
        let loadAssembly name =
            match loadedAssemblies.TryGetValue name with
            | (true, assembly) -> assembly
            | (false, _) ->
                let assembly = Assembly.Load (AssemblyName name)
                let parameters = ReaderParameters ()
                parameters.AssemblyResolver <- this

                let assembly = 
                    let attribute = assembly.GetCustomAttribute<SafetySharpAssemblyAttribute> ()
                    if attribute = null then
                        AssemblyDefinition.ReadAssembly (assembly.Location, parameters)
                    else
                        use stream = assembly.GetManifestResourceStream attribute.ResourceName
                        if stream = null then
                            AssemblyDefinition.ReadAssembly (assembly.Location, parameters)
                        else
                            AssemblyDefinition.ReadAssembly (stream, parameters)

                loadedAssemblies.Add (name, assembly)
                assembly

        do types 
            |> Seq.distinct
            |> Seq.iter (fun t -> 
                let assemblyDefinition = loadAssembly t.Assembly.FullName

                // Add the type and all of its base types to the dictionary, if we haven't added them already
                let rec add (t : System.Type) =
                    if typeReferences.ContainsKey t |> not then
                        typeReferences.Add (t, assemblyDefinition.MainModule.Import t)
                        if t.BaseType <> null then add t.BaseType
                        t.GetInterfaces () |> Array.iter add

                add t
            )

        /// Resolves the assembly definition for the given assembly name.
        override this.Resolve (name : AssemblyNameReference) : AssemblyDefinition = 
            loadAssembly name.FullName
            
        /// Gets the type reference for the given object.
        member this.GetTypeReference (o : obj) =
            typeReferences.[o.GetType ()]

        /// Gets the type reference for the given type.
        member this.GetTypeReference t =
            typeReferences.[t]

        /// Resolve the field definition for the given field info.
        member this.Resolve (f : FieldInfo) =
            this.GetTypeReference(f.DeclaringType).Module.Import(f).Resolve ()

        /// Resolve the method definition for the given method info.
        member this.Resolve (m : MethodInfo) =
            this.GetTypeReference(m.DeclaringType).Module.Import(m).Resolve ()

        /// Maps the given method name of the given type back to a method info.
        member this.UnmapMethod (t : Type) (methodName : string) =
            let typeDefinition = this.GetTypeReference t
            let manglingStart = methodName.IndexOf Renaming.InheritanceToken
            let unmangledPart = if manglingStart = -1 then methodName else methodName.Substring (0, manglingStart)

            ReflectionExtensions.GetMethods(t, typeof<obj>)
            |> Seq.filter (fun m -> m.Name.StartsWith unmangledPart)
            |> Seq.map (fun m -> (m, typeDefinition.Module.Import(m).Resolve ()))
            |> Seq.find (fun (info, definition) -> Renaming.getUniqueMethodName definition = methodName)
            |> fst

        /// Gets the type object for the type with the given name implemented by the given type.
        member this.GetImplementedType implementingType implementedType =
            let interfaceMatches t = 
                let reference = this.GetTypeReference t
                reference.FullName = implementedType || reference.Resolve().FullName = implementedType

            let classMatches t = 
                let reference = this.GetTypeReference t
                if reference.FullName = implementedType || reference.Resolve().FullName = implementedType then true
                else
                    // Special case when X<T> calls one of its own methods, for instance. In that case, implementedType == "X<T>", i.e.,
                    // the type parameter is not resolved but we still want to match the "X" class 
                    let typeListStart = implementedType.IndexOf '<'
                    if typeListStart = -1 then false
                    else
                        reference.IsGenericInstance && reference.Resolve().FullName.StartsWith (implementedType.Substring (0, typeListStart))

            let rec get t =
                if classMatches t then t
                else
                    let baseType = if t.BaseType <> null then get t.BaseType else null
                    if baseType <> null then baseType
                    else
                        match t.GetInterfaces () |> Seq.tryFind interfaceMatches with
                        | None -> null
                        | Some t -> t

            let t = get implementingType
            if t = null then invalidOp "Type '%s' does not implement or inherit '%s'." implementingType.FullName implementedType
            t