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

namespace SafetySharp.Models

open Mono.Cecil
open SafetySharp
open SafetySharp.Modeling
open SafetySharp.Runtime
open SafetySharp.Reflection
open System.Reflection
open System
open System.Globalization

[<AutoOpen>]
module Extensions =
    
    type Component with
        /// Gets the initial values of given field.
        member internal this.GetInitialValuesOfField (field : FieldDefinition) =
            nullArg field "field"

            // We have to find a FieldInfo instance that resolves to the given FieldDefinition
            match this.Metadata.Fields |> Seq.tryFind (fun f -> (field.Module.Import(f.FieldInfo).Resolve ()) = field) with
            | Some f -> f.InitialValues |> Seq.toList |> List.map (fun v -> 
                if v.GetType().IsEnum then (v :?> IConvertible).ToInt32(CultureInfo.InvariantCulture) :> obj else v)
            | None   -> 
                invalidArg true "field" "Unable to retrieve initial values for field '%s'." field.FullName
                [] // Required, but cannot be reached

        member this.Slot 
            with get () : int =
                if this.Metadata.ParentComponent = null then -1
                else this.Metadata.ParentComponent.Component.Subcomponents |> List.findIndex ((=) this) 

        member internal this.Name
            with get () : string = 
                let fieldName = if this.ParentField <> null then this.ParentField.Name else sprintf "%s%d" (this.GetType().Name) this.Slot
                let name = if this.Parent <> null then sprintf "%s.%s" (this.Parent.Name) fieldName else "R"
                if this.Slot = -1 then name
                else sprintf "%s@%d" name this.Slot

        /// Gets the unmangled, non-unique name of the component instance. Returns the empty string if no component name could be determined.
        member internal this.UnmangledName
            with get () : string = 
                let parentName = if this.Metadata.ParentComponent <> null then this.Metadata.ParentComponent.Component.UnmangledName else ""
                sprintf "%s%s" parentName this.ParentField.Name

        /// Gets the <see cref="Component" /> instances that are direct subcomponents of the current instance.
        member internal this.Subcomponents 
            with get () = 
                this.Metadata.Subcomponents |> Seq.map (fun c -> c.Component) |> Seq.toList

        /// Gets the port bindings of the component.
        member internal this.Bindings
            with get () =
                this.Metadata.Bindings |> Seq.toList

        /// Gets the faults of the component.
        member internal this.Faults
            with get () =
                this.Metadata.Faults |> Seq.toList

        /// Gets the parent component of the component within the hierarchy or null if the component represents the root of the hierarchy.
        member internal this.Parent 
            with get() : Component =
                if this.Metadata.ParentComponent = null then null else this.Metadata.ParentComponent.Component

        /// Gets the field of the parent component the component is stored in. Returns null for root components.
        member internal this.ParentField
            with get () : FieldInfo =
                if this.Metadata.ParentComponent = null then null
                else
                    let c = this.Metadata.ParentComponent.Component
                    let fields = c.GetType().GetFields(BindingFlags.Instance ||| BindingFlags.NonPublic ||| BindingFlags.Public)
                    match fields |> Array.tryFind (fun f -> f.GetValue(c) = (this :> obj)) with
                    | Some f -> f
                    | None -> null

    type Model with
        /// Gets the metadata provider for the model.
        member internal this.GetMetadataProvider () =
            let metadataTypes = seq {
                yield! this.Components |> Seq.map (fun c -> c.GetType ())
                yield! this.Components |> Seq.collect (fun (c : Component) -> c.Metadata.Faults |> Seq.map (fun f -> f.GetType ()))
            }
            
            MetadataProvider (metadataTypes |> Seq.toList)

        member this.FinalizeMetadata () =
            this.Seal()

        /// Gets the root <see cref="Component" />s of the model.
        member internal this.Roots 
            with get () = 
                []

        /// Gets the synthesized root component of the model.
        member internal this.SynthesizedRoot
            with get() =
                this.Metadata.RootComponent.Component

        /// Gets all <see cref="Component" />s contained in the model configuration.
        member internal this.Components 
            with get () = 
                this.Metadata.Components |> Seq.map (fun c -> c.Component) |> Seq.toList

        /// Returns the component with the given mangled name.
        member internal this.FindComponent mangledName =
            //if mangledName = Component.S.Name then synthesizedRoot
            //else 
            this.Components |> List.find (fun c -> c.Name = mangledName)

        /// Returns the type of the component with the given mangled name.
        member internal this.GetTypeOfComponent mangledName =
            this.FindComponent(mangledName).GetType ()