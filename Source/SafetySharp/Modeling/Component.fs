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
open System.Dynamic
open System.Globalization
open System.Linq
open System.Linq.Expressions
open System.Reflection
open System.Runtime.CompilerServices
open System.Runtime.InteropServices
open SafetySharp
open SafetySharp.Modeling.CompilerServices
open Mono.Cecil

/// Represents an interface that must be implemented by all components.
[<AllowNullLiteral>]
type IComponent = 
    /// Updates the internal state of the component.
    abstract member Update : unit -> unit

    /// Gets all required ports declared by the component.
    [<Dynamic>]
    abstract member RequiredPorts : obj

    /// Gets all provided ports declared by the component.
    [<Dynamic>]
    abstract member ProvidedPorts : obj

/// Provides access to a non-public member of a component.
type internal IMemberAccess =
    /// Gets the accessed component instance.
    abstract member Component : IComponent

    /// Gets the name of the accessed member.
    abstract member MemberName : string

/// <summary>
///     Provides access to a non-public member of a component.
/// </summary>
/// <typeparam name="T">The type of the accessed member.</typeparam>
type MemberAccess<'T> internal (component', memberName) =
    let componentType = component'.GetType ()
    let bindingFlags = BindingFlags.Instance ||| BindingFlags.FlattenHierarchy ||| BindingFlags.Public ||| BindingFlags.NonPublic
    let fieldInfo = componentType.GetField (memberName, bindingFlags)
    let propertyInfo = componentType.GetProperty (memberName, bindingFlags)

    do if fieldInfo = null && propertyInfo = null then
        invalidOp "Component of type '%s' has no member with name '%s'." componentType.FullName memberName

    do if propertyInfo <> null && not propertyInfo.CanRead then
        invalidOp "Property '%s.%s' is write-only." componentType.FullName memberName

    let memberType = if fieldInfo <> null then fieldInfo.FieldType else propertyInfo.PropertyType
    do if memberType <> typeof<'T> then
        invalidOp "Expected '%s.%s' to be of type '%s', but actual type is '%s'." componentType.FullName memberName memberType.FullName typeof<'T>.FullName

    interface IMemberAccess with
        /// Gets the accessed component instance.
        override this.Component = component'

        /// Gets the name of the accessed member.
        override this.MemberName = memberName

    /// <summary>
    ///     Gets the current. value of the accessed member.
    /// </summary>
    /// <param name="access">The member access the value should be retrieved for.</param>
    /// <returns>Returns the current value of the accessed member.</returns>
    static member op_Implicit (access : MemberAccess<'T>) =
        access.Value

    /// Gets the current value of the accessed member.
    member internal this.Value = 
        if fieldInfo <> null then
            fieldInfo.GetValue component' :?> 'T
        else
            propertyInfo.GetValue component' :?> 'T

/// Represents a base class for all faults.
[<AbstractClass; AllowNullLiteral>]
type Fault () =
    class end

/// Represents a base class for all components.
[<AbstractClass; AllowNullLiteral>] 
type Component internal (components : Component list, bindings : List<PortBinding>) =
    
    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Component state and metadata
    // ---------------------------------------------------------------------------------------------------------------------------------------

    let mutable isSealed = false
    let mutable name = String.Empty
    let mutable slot = 0
    let mutable parent : Component = null
    let fields = Dictionary<FieldInfo, obj list> ()
    let mutable subcomponents = components
    let mutable parentField : FieldInfo = null

    let requiresNotSealed () = invalidCall isSealed "Modifications of the component metadata are only allowed during object construction."
    let requiresIsSealed () = invalidCall (not <| isSealed) "Cannot access the component metadata as it might not yet be complete."

    new () = Component ([], List<PortBinding> ())

    interface IComponent with
        /// Updates the internal state of the component.
        member this.Update () = this.Update ()

        /// Gets all required ports declared by the component.
        [<Dynamic>]
        member this.RequiredPorts with get () = this.RequiredPorts

        /// Gets all provided ports declared by the component.
        [<Dynamic>]
        member this.ProvidedPorts with get () = this.ProvidedPorts

    /// Updates the internal state of the component.
    abstract member Update : unit -> unit
    default this.Update () = ()

    /// Gets all required ports declared by the component.
    [<Dynamic>]
    member this.RequiredPorts with get () = invalidOp "This method cannot be called outside of a port binding expression."

    /// Gets all provided ports declared by the component.
    [<Dynamic>]
    member this.ProvidedPorts with get() = invalidOp "This method cannot be called outside of a port binding expression."

    /// Gets a value indicating whether the metadata has been finalized and any modifications of the metadata are prohibited.
    member internal this.IsMetadataFinalized = isSealed

    /// Gets the name of the synthesized root component.
    static member internal SynthesizedRootName = "R"

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Internal access
    // ---------------------------------------------------------------------------------------------------------------------------------------

    /// <summary>
    ///     Allows access to a non-public member of the component.
    /// </summary>
    /// <typeparam name="T">The type of the accessed member.</typeparam>
    /// <param name="memberName">The name of the member that should be accessed.</param>
    /// <returns>Returns an <see cref="MemberAccess{T}" /> instance that can be used to access the non-public member.</returns>
    member this.Access<'T> memberName =
        nullOrWhitespaceArg memberName "memberName"
        MemberAccess<'T> (this, memberName)

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Methods that can only be called during metadata initialization
    // ---------------------------------------------------------------------------------------------------------------------------------------

    /// Establishes the given port binding. By default, the binding is instantenous; invoke the <see cref="PortBinding.Delayed" /> method
    /// on the <see cref="PortBinding" /> instance returned by this method to create a delayed binding instead.
    member this.Bind (binding : PortBinding) =
        nullArg binding "binding"
        binding.Binder <- this
        bindings.Add binding
        binding

    /// <summary>
    ///     Sets the initial values of a field of the component instance.
    /// </summary>
    /// <param name="field">[LiftExpression] A field of the component.</param>
    /// <param name="initialValues">The initial values of the field.</param>
    member this.SetInitialValues<'T when 'T :> obj> ([<LiftExpression>] field : 'T, [<ParamArray>] initialValues : 'T array) =
        invalidUnliftedCall ()

    /// <summary>
    ///     Sets the initial values of a field of the component instance.
    /// </summary>
    /// <param name="field">A field of the component.</param>
    /// <param name="initialValues">The initial values of the field.</param>
    member this.SetInitialValues<'T when 'T :> obj> (field : Expression<Func<'T>>, [<ParamArray>] initialValues : 'T array) =
        nullArg field "field"
        nullArg initialValues "initialValues"
        invalidArg (initialValues.Length <= 0) "initialValues" "At least one value must be provided."
        invalidArg (not <| field.Body :? MemberExpression) "field" "Expected a reference to a field of the component."
        requiresNotSealed ()

        match (field.Body :?> MemberExpression).Member with
        | :? FieldInfo as fieldInfo ->
            // Check if the field is actually defined or inherited by the component
            if not (fieldInfo.DeclaringType.IsAssignableFrom <| this.GetType ()) then
                invalidArg true "field" "Expected a reference to a field of the component."

            fields.[fieldInfo] <-
                if fieldInfo.FieldType.IsEnum then
                    let containsInvalidLiteral = initialValues |> Seq.tryFind (fun value -> not <| Enum.IsDefined (fieldInfo.FieldType, value))
                    if containsInvalidLiteral.IsSome then
                        invalidArg true "initialValues" "Invalid enumeration value '%A'." containsInvalidLiteral.Value
                    initialValues |> Seq.map (fun value -> ((value :> obj) :?> IConvertible).ToInt32 (CultureInfo.InvariantCulture) :> obj) |> List.ofSeq
                else
                    initialValues |> Seq.cast<obj> |> List.ofSeq

            let random = Random();
            fieldInfo.SetValue(this, initialValues.[random.Next(0, initialValues.Length)]);
        | _ -> invalidArg true "field" "Expected a reference to a field of the component."

    /// Finalizes the component's metadata, disallowing any future metadata modifications.
    member internal this.FinalizeMetadata (?parentComponent : Component, ?componentName : string, ?componentSlot : int, ?field : FieldInfo) =
        invalidCall isSealed "The component's metadata has already been finalized."

        isSealed <- true
        parent <- defaultArg parentComponent null
        name <- defaultArg componentName String.Empty
        slot <- defaultArg componentSlot -1
        parentField <- defaultArg field null

        // Retrieve the non-subcomponent fields of the component
        Reflection.getFields (this.GetType ()) typeof<Component>
        |> Seq.where (fun field -> not field.IsStatic && not <| typeof<IComponent>.IsAssignableFrom field.FieldType && not <| fields.ContainsKey field)
        |> Seq.iter (fun field ->
            let value =
                if field.FieldType.IsEnum then
                    (field.GetValue(this) :?> IConvertible).ToInt32 (CultureInfo.InvariantCulture) :> obj
                else
                    field.GetValue this
            fields.Add (field, [value])
        )

        // Finalize the component's bindings
        bindings |> Seq.iter (fun binding -> binding.FinalizeMetadata ())

        // Retrieve the subcomponents of the component; we skip that step when the subcomponents have already been provided 
        // via the constructor (namely: for the synthesized root component)
        if subcomponents |> List.length = 0 then
            let subcomponentMetadata = 
                Reflection.getFields (this.GetType ()) typeof<Component>
                |> Seq.where (fun field -> not field.IsStatic && typeof<IComponent>.IsAssignableFrom field.FieldType)
                |> Seq.map (fun field -> (field, field.GetValue(this)))
                |> Seq.where (fun (field, component') -> component' <> null)
                |> Seq.map (fun (field, component') -> (field, component' :?> Component))
                |> Seq.toList

            subcomponents <- subcomponentMetadata |> List.map snd
            subcomponentMetadata
            |> List.iteri (fun idx (field, component') -> 
                // Make sure that we won't finalize the same component twice (might happen when components are shared, will be detected later)
                if not component'.IsMetadataFinalized then
                    component'.FinalizeMetadata (this, field.Name, idx, field)
            )

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Methods that can only be called after metadata initialization
    // ---------------------------------------------------------------------------------------------------------------------------------------

    /// Gets the initial values of given field.
    member internal this.GetInitialValuesOfField (field : FieldDefinition) =
        nullArg field "field"
        requiresIsSealed ()

        // We have to find a FieldInfo instance that resolves to the given FieldDefinition
        match fields.Keys |> Seq.tryFind (fun info -> (field.Module.Import(info).Resolve ()) = field) with
        | Some f -> fields.[f]
        | None   -> 
            invalidArg true "field" "Unable to retrieve initial values for field '%s'." field.FullName
            [] // Required, but cannot be reached

    /// Gets the unique name of the component instance. Returns the empty string if no component name could be determined.
    member internal this.Name
        with get () : string = 
            requiresIsSealed ()
            let name = if this.Parent <> null then sprintf "%s.%s" (this.Parent.Name) name else sprintf "%s" name
            if slot = -1 then name
            else sprintf "%s@%d" name slot

    /// Gets the unmangled, non-unique name of the component instance. Returns the empty string if no component name could be determined.
    member internal this.UnmangledName
        with get () : string = 
            requiresIsSealed ()
            if this.Parent <> null then
                sprintf "%s.%s" (this.Parent.UnmangledName) name
            else
                name.Substring (Component.SynthesizedRootName.Length + 1)

    /// Gets the <see cref="Component" /> instances that are direct subcomponents of the current instance.
    member internal this.Subcomponents 
        with get () = 
            requiresIsSealed ()
            subcomponents

    /// Gets the port bindings of the component.
    member internal this.Bindings
        with get () =
            requiresIsSealed ()
            bindings |> Seq.toList

    /// Gets the parent component of the component within the hierarchy or null if the component represents the root of the hierarchy.
    member internal this.Parent 
        with get() : Component =
            requiresIsSealed ()
            parent

    /// Gets the field of the parent component the component is stored in. Returns null for root components.
    member internal this.ParentField
        with get () : FieldInfo =
            requiresIsSealed ()
            parentField

/// Represents the synthesized root of the component hierarchy created by a model.
type internal SynthesizedRootComponent (components, bindings) as this =
    inherit Component (components, bindings)
    do this.FinalizeMetadata (null, Component.SynthesizedRootName)