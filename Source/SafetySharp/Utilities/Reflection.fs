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
open Mono.Cecil

/// Provides helper functions for working with the reflection APIs.
module internal Reflection =

    /// The name of the resource that stores the embedded original S# assembly.
    [<Literal>]
    let EmbeddedAssembly = "OriginalAssembly"

    /// Gets all members of the given object recursively, going up the inheritance chain; unfortunately, the reflection APIs
    /// do not return private members of base classes, even with BindingFlags.FlattenHierarchy.
    let rec private getMembers selector (typeInfo : Type) (inheritanceRoot : Type) = seq {
        if typeInfo.BaseType <> null && typeInfo.BaseType <> inheritanceRoot then
            yield! getMembers selector typeInfo.BaseType inheritanceRoot
        
        let flags = BindingFlags.Static ||| BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.DeclaredOnly
        yield! selector typeInfo flags
    }

    /// Gets all fields declared by the given type or one of its base types up to the given root of the inheritance hierarchy.
    let getFields typeInfo inheritanceRoot = 
        getMembers (fun t b -> t.GetFields b) typeInfo inheritanceRoot

    /// Gets all properties declared by the given type or one of its base types up to the given root of the inheritance hierarchy.
    let getProperties typeInfo inheritanceRoot = 
        getMembers (fun t b -> t.GetProperties b) typeInfo inheritanceRoot

    /// Gets all methods declared by the given type or one of its base types up to the given root of the inheritance hierarchy.
    let getMethods typeInfo inheritanceRoot = 
        getMembers (fun t b -> t.GetMethods b) typeInfo inheritanceRoot

    /// Gets a value indicating whether the given member info is marked with an instance of the given attribute.
    let hasAttribute<'T> (info : MemberInfo) =
        info.GetCustomAttribute (typeof<'T>, false) <> null

    /// Gets the given type's method that implements the given interface method.
    let getImplementingMethod (typeInfo : Type) (interfaceMethod : MethodInfo) =
        let map = typeInfo.GetInterfaceMap interfaceMethod.DeclaringType
        let index = map.InterfaceMethods |> Array.findIndex ((=) interfaceMethod)
        map.TargetMethods.[index]

    /// Gets the given type's method that overrides the given non-interface method. If the type does not override the method,
    /// the given method is returned.
    let rec getOverridingMethod (typeInfo : Type) (baseMethod : MethodInfo) =
        let methods = typeInfo.GetMethods (BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.DeclaredOnly)
        match methods |> Array.tryFind (fun m -> m = baseMethod || m.GetBaseDefinition () = baseMethod) with
        | Some m -> m
        | None ->
            if typeInfo.BaseType <> null then getOverridingMethod typeInfo.BaseType baseMethod
            else baseMethod

    /// Provides an extension method that returns all methods excluding all constructors.
    type private TypeDefinition with
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
                    use stream = assembly.GetManifestResourceStream EmbeddedAssembly
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

        /// Maps the given method name of the given component back to a method info.
        member this.UnmapMethod (o : obj) (methodName : string) =
            let typeDefinition = this.GetTypeReference o
            let unmangledPart = methodName.Substring (0, methodName.IndexOf Renaming.InheritanceToken)

            getMethods (o.GetType ()) typeof<obj>
            |> Seq.filter (fun m -> m.Name.StartsWith unmangledPart)
            |> Seq.map (fun m -> (m, typeDefinition.Module.Import(m).Resolve ()))
            |> Seq.find (fun (info, definition) -> Renaming.getUniqueMethodName definition = methodName)
            |> fst