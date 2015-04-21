﻿// The MIT License (MIT)
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

namespace SafetySharp.Modeling

open System
open System.Collections.Generic
open System.Linq
open System.Linq.Expressions
open System.Reflection
open System.Runtime.InteropServices
open SafetySharp
open SafetySharp.Reflection

/// Raised when a component is found in multiple locations of a component tree.
type SharedComponentsException internal (components : Component list) =
    inherit Exception ("One or more components have been found in multiple locations of the component tree. \
                        Check the 'Components' property of this exception instance for the shared component instances.")

    /// Gets the component instances that were found in multiple locations of a component tree.
    member this.Components = components |> List.toArray

/// Represents a base class for all models.
[<AllowNullLiteral>]
type Model private () =

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Model state and metadata
    // ---------------------------------------------------------------------------------------------------------------------------------------

    let mutable roots : Component list = []
    let mutable components : Component list = []
    let mutable isSealed = false
    let mutable synthesizedRoot : Component = null
    let mutable metadataProvider : MetadataProvider = null
    let bindings = List<PortBinding> ()
    let requiresNotSealed () = invalidCall isSealed "Modifications of the model metadata are only allowed during object construction."
    let requiresIsSealed () = invalidCall (not isSealed) "Cannot access the model metadata as it might not yet be complete."

    let rec getAllComponents (checkedComponents : HashSet<Component>) (component' : Component) =
        seq {
            yield component'
            if checkedComponents.Add component' then
                yield! component'.Subcomponents |> Seq.collect (getAllComponents checkedComponents)
        }

    /// <summary>
    ///    Initializes a new instance.
    /// </summary>
    /// <param name="rootComponents">The root components of the model.</param>
    new ([<ParamArray>] rootComponents : Component array) as this =
        Model ()
        then 
            if rootComponents <> null && rootComponents.Length > 0 then this.SetRootComponents rootComponents

    /// Gets a value indicating whether the metadata has been finalized and any modifications of the metadata are prohibited.
    member internal this.IsMetadataFinalized = isSealed

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Methods that can only be called during metadata initialization
    // ---------------------------------------------------------------------------------------------------------------------------------------

    /// Sets the <paramref name="rootComponents" /> of the model.
    member this.SetRootComponents ([<ParamArray>] rootComponents : Component array) =
        nullArg rootComponents "rootComponents"
        invalidArg (rootComponents.Length <= 0) "rootComponents" "There must be at least one root component."
        invalidCall (components <> []) "The root components have already been set."
        invalidCall isSealed "The model's metadata has already been finalized."

        // Disallow future modifications of the components' metadata
        rootComponents |> Seq.iteri (fun index component' -> 
            // Make sure that we won't finalize the same component twice (might happen when components are shared, will be detected later)
            if not component'.IsMetadataFinalized then
                // Add the index to the name to disambiguate roots in execption messages
                component'.FinalizeMetadata (null, sprintf "%s.Root%d" Component.SynthesizedRootName index, index) 
        )

        // Store the root components and collect all components of the model
        roots <- rootComponents |> List.ofSeq
        let set = HashSet<Component> ()
        components <- roots |> Seq.collect (getAllComponents set) |> List.ofSeq

        // Ensure that there are no shared components
        let sharedComponents =
            components 
            |> Seq.groupBy id
            |> Seq.filter (fun (key, values) -> values |> Seq.length > 1)
            |> Seq.map fst
            |> List.ofSeq

        if sharedComponents |> List.length > 0 then
            SharedComponentsException sharedComponents |> raise

    /// Finalizes the models's metadata, disallowing any future metadata modifications.
    member internal this.FinalizeMetadata () =
        invalidCall (components = []) "No root components have been set for the model."
        requiresNotSealed ()

        isSealed <- true
        synthesizedRoot <- SynthesizedRootComponent (roots, bindings)
        metadataProvider <- MetadataProvider (typeof<SynthesizedRootComponent> :: (components |> List.map (fun c -> c.GetType ())))

    /// Establishes the given port binding. By default, the binding is instantenous; invoke the <see cref="PortBinding.Delayed" /> method
    /// on the <see cref="PortBinding" /> instance returned by this method to create a delayed binding instead.
    member this.Bind (binding : PortBinding) =
        nullArg binding "binding"
        requiresNotSealed ()

        binding.Binder <- this
        bindings.Add binding
        binding

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Methods that can only be called after metadata initialization
    // ---------------------------------------------------------------------------------------------------------------------------------------

    /// Gets the root <see cref="Component" />s of the model.
    member internal this.Roots 
        with get () = 
            requiresIsSealed ()
            roots

    /// Gets the synthesized root component of the model.
    member internal this.SynthesizedRoot
        with get() =
            requiresIsSealed ()
            synthesizedRoot

    /// Gets all <see cref="Component" />s contained in the model configuration.
    member internal this.Components 
        with get () = 
            requiresIsSealed ()
            components

    /// Returns the component with the given mangled name.
    member internal this.FindComponent mangledName =
        requiresIsSealed ()
        if mangledName = synthesizedRoot.Name then synthesizedRoot
        else components |> List.find (fun c -> c.Name = mangledName)

    /// Returns the type of the component with the given mangled name.
    member internal this.GetTypeOfComponent mangledName =
        requiresIsSealed ()
        this.FindComponent(mangledName).GetType ()

    /// Gets the metadata provider of the model.
    member internal this.MetadataProvider
        with get () =
            requiresIsSealed ()
            metadataProvider

[<AutoOpen>]
module internal Extensions =
    type PortBinding with
        /// Gets the user-friendly name of the binder.
        member internal this.BinderName = 
            match this.Binder with
            | :? Component as c -> c.UnmangledName
            | :? Model -> "Model"
            | _ -> "<unknown>"