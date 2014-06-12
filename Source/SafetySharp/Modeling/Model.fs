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

namespace SafetySharp.Modeling

open System
open System.Collections.Generic
open System.Linq
open System.Linq.Expressions
open System.Reflection
open System.Runtime.InteropServices
open SafetySharp.Utilities

/// Raised when a component is found in multiple locations of a component tree.
type SharedComponentsException (components : Component list) =
    inherit Exception ("One or more components have been found in multiple locations of the component tree.")

    /// Gets the component instances that was found in multiple locations of a component tree.
    member this.Components = components

/// Represents a base class for all models.
[<AbstractClass>]
type Model () =

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Model state and metadata
    // ---------------------------------------------------------------------------------------------------------------------------------------

    let mutable (partitionRoots : Component list) = []
    let mutable (components : Component list) = []
    let mutable isSealed = false

    let requiresNotSealed () = Requires.That (not isSealed) "Modifications of the model metadata are only allowed during object construction."
    let requiresIsSealed () = Requires.That isSealed "Cannot access the model metadata as it might not yet be complete."

    let rec getAllComponents (component' : Component) =
        seq {
            yield component'
            yield! component'.Subcomponents |> Seq.collect getAllComponents
        }

    /// Gets a value indicating whether the metadata has been finalized and any modifications of the metadata are prohibited.
    member internal this.IsMetadataFinalized = isSealed

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Methods that can only be called during metadata initialization
    // ---------------------------------------------------------------------------------------------------------------------------------------

    /// Sets the <paramref name="rootComponents" /> of the model's partitions.
    member this.SetPartitions ([<ParamArray>] rootComponents : Component array) =
        Requires.NotNull rootComponents "rootComponents"
        Requires.ArgumentSatisfies (rootComponents.Length > 0) "rootComponents" "There must be at least one partition root."
        Requires.That (components = []) "This method can only be called once on any given model instance."
        requiresNotSealed ()

        // Disallow future modifications of the components' metadata
        rootComponents |> Seq.iteri (fun index component' -> 
            // Make sure that we won't finalize the same component twice (might happen when components are shared, will be detected later)
            if not component'.IsMetadataFinalized then
                component'.FinalizeMetadata ("Root" + index.ToString())
        )

        // Store the partition roots and collect all components of the model
        partitionRoots <- rootComponents |> List.ofSeq
        components <- partitionRoots |> Seq.collect getAllComponents |> List.ofSeq

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
        Requires.That (components <> []) "No partition roots have been set for the model."
        requiresNotSealed ()

        isSealed <- true

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Methods that can only be called after metadata initialization
    // ---------------------------------------------------------------------------------------------------------------------------------------

    /// Gets the partition root <see cref="Component" />s of the configuration.
    member internal this.PartitionRoots 
        with get () = 
            requiresIsSealed ()
            partitionRoots

    /// Gets all <see cref="Component" />s contained in the model configuration.
    member internal this.Components 
        with get () = 
            requiresIsSealed ()
            components