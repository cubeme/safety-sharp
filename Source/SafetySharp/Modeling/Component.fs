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

/// Represents a base class for all components.
[<AbstractClass>]
type Component () =

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Component state and metadata
    // ---------------------------------------------------------------------------------------------------------------------------------------

    let mutable isSealed = false
    let mutable name = String.Empty
    let mutable (subcomponents : Component list) = []
    let fields = Dictionary<string, obj list> ()

    let requiresNotSealed () = Requires.That (not isSealed) "Modifications of the component metadata are only allowed during object construction."
    let requiresIsSealed () = Requires.That isSealed "Cannot access the component metadata as it might not yet be complete."

    /// Gets a value indicating whether the metadata has been finalized and any modifications of the metadata are prohibited.
    member internal this.IsMetadataFinalized = isSealed

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Update method and interface implementation
    // ---------------------------------------------------------------------------------------------------------------------------------------

    /// Invoked exactly once during each system step.
    abstract member Update : unit -> unit
    default this.Update () = ()

    interface IComponent

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Methods that can only be called during metadata initialization
    // ---------------------------------------------------------------------------------------------------------------------------------------

    /// Adds metadata about a field of the component to the <see cref="Component" /> instance.
    member this.SetInitialValues<'T> (field : Expression<Func<'T>>, [<ParamArray>] initialValues : 'T array) =
        Requires.NotNull field "field"
        Requires.NotNull initialValues "initialValues"
        Requires.ArgumentSatisfies (initialValues.Length > 0) "initialValues" "At least one value must be provided."
        Requires.OfType<MemberExpression> field.Body "field" "Expected a lambda expression of the form '() => field'."
        requiresNotSealed ()

        match (field.Body :?> MemberExpression).Member with
        | :? FieldInfo as fieldInfo ->
            fields.[fieldInfo.Name] <- initialValues |> Seq.cast<obj> |> List.ofSeq

            let random = Random();
            fieldInfo.SetValue(this, initialValues.[random.Next(0, initialValues.Length)]);
        | _ -> Requires.ArgumentSatisfies false "field" "Expected a lambda expression of the form '() => field'."

    /// Finalizes the component's metadata, disallowing any future metadata modifications.
    member internal this.FinalizeMetadata (?componentName : string) =
        requiresNotSealed ()

        isSealed <- true
        name <- defaultArg componentName String.Empty

        this.GetType().GetFields(BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic)
        |> Seq.where (fun field -> not <| typeof<IComponent>.IsAssignableFrom(field.FieldType) && not <| fields.ContainsKey(field.Name))
        |> Seq.iter (fun field -> fields.Add (field.Name, [field.GetValue this]))

        let subcomponentMetadata = 
            this.GetType().GetFields(BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic)
            |> Seq.where (fun field -> typeof<IComponent>.IsAssignableFrom(field.FieldType))
            |> Seq.map (fun field -> (field, field.GetValue(this)))
            |> Seq.where (fun (field, component') -> not <| obj.ReferenceEquals(component', null))
            |> Seq.map (fun (field, component') -> (field, component' :?> Component))
            |> List.ofSeq

        subcomponents <- subcomponentMetadata |> List.map snd
        subcomponentMetadata
        |> List.iter (fun (field, component') -> 
            // Make sure that we won't finalize the same component twice (might happen when components are shared, will be detected later)
            if not component'.IsMetadataFinalized then
                component'.FinalizeMetadata field.Name
        )

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Methods that can only be called after metadata initialization
    // ---------------------------------------------------------------------------------------------------------------------------------------

    /// Gets the initial values of the field with name <paramref name="fieldName" />.
    member internal this.GetInitialValuesOfField fieldName =
        Requires.NotNullOrWhitespace fieldName "fieldName"
        requiresIsSealed ()

        let (result, initialValues) = fields.TryGetValue fieldName
        Requires.ArgumentSatisfies result "fieldName" (sprintf "A field with name '%s' does not exist." fieldName)

        initialValues

    /// <summary>
    /// Gets the subcomponent with the given name.
    /// </summary>
    member internal this.GetSubcomponent name =
        Requires.NotNullOrWhitespace name "name"
        requiresIsSealed ()

        let subcomponent = subcomponents |> List.tryFind (fun component' -> component'.Name = name)
        match subcomponent with
        | Some subcomponent -> subcomponent
        | None ->
            Requires.ArgumentSatisfies false "name" (sprintf "A sub component with name '%s' does not exist." name)
            subcomponent.Value // Required, but cannot be reached

    /// Gets or sets the name of the component instance. Returns the empty string if no component name could be determined.
    member internal this.Name 
        with get () = 
            requiresIsSealed ()
            name

    /// Gets the <see cref="Component" /> instances that are direct subcomponents of the current instance.
    member internal this.Subcomponents 
        with get () = 
            requiresIsSealed ()
            subcomponents

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Choose methods
    // ---------------------------------------------------------------------------------------------------------------------------------------
   
    static member Choose<'T> ([<Out>] result : 'T byref, [<ParamArray>] values: 'T array) : 'T =
        raise <| NotImplementedException ()

    static member ChooseFromRange ([<Out>] result : int byref, inclusiveLowerBound : int, inclusiveUpperBound : int) : int =
        raise <| NotImplementedException ()

    static member ChooseFromRange ([<Out>] result : decimal byref, inclusiveLowerBound : decimal, inclusiveUpperBound : decimal) : decimal =
        raise <| NotImplementedException ()

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // The following methods are never invoked at runtime but their definition is required during transformation.                  
    // ---------------------------------------------------------------------------------------------------------------------------------------
    
    static member Choose<'T when 'T : struct> () : 'T =
        raise <| NotSupportedException ()

    static member Choose<'T> ([<ParamArray>] values : 'T array) : 'T =
        raise <| NotSupportedException ()

    static member ChooseFromRange (inclusiveLowerBound : int, inclusiveUpperBound : int) : int =
        raise <| NotSupportedException ()

    static member ChooseFromRange (inclusiveLowerBound : decimal, inclusiveUpperBound : decimal) : decimal =
        raise <| NotSupportedException ()