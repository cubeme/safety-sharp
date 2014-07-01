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
open System.Globalization
open System.Linq
open System.Linq.Expressions
open System.Reflection
open System.Runtime.InteropServices
open SafetySharp.Utilities

/// Represents a marker interface for components.
[<AllowNullLiteral>]
type IComponent =
    /// Gets the name of the component instance. Returns the empty string if no component name could be determined.
    abstract member Name : string

/// Provides access to a non-public member of a component.
type IMemberAccess =
    /// Gets the accessed component instance.
    abstract member Component : IComponent

    /// Gets the name of the accessed member.
    abstract member MemberName : string

/// Provides access to a non-public member of a component.
type MemberAccess<'T> internal (component' : IComponent, memberName : string) =
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

    /// Gets the current value of the accessed member.
    static member op_Implicit (access : MemberAccess<'T>) =
        access.Value

    /// Gets the current value of the accessed member.
    member this.Value = 
        if fieldInfo <> null then
            fieldInfo.GetValue component' :?> 'T
        else
            propertyInfo.GetValue component' :?> 'T

/// Represents a base class for all components.
[<AbstractClass; AllowNullLiteral>] 
type Component () =

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Component state and metadata
    // ---------------------------------------------------------------------------------------------------------------------------------------

    let mutable isSealed = false
    let mutable name = String.Empty
    let mutable (subcomponents : Component list) = []
    let fields = Dictionary<string, obj list> ()

    let requiresNotSealed () = invalidCall isSealed "Modifications of the component metadata are only allowed during object construction."
    let requiresIsSealed () = invalidCall (not <| isSealed) "Cannot access the component metadata as it might not yet be complete."

    /// Gets a value indicating whether the metadata has been finalized and any modifications of the metadata are prohibited.
    member internal this.IsMetadataFinalized = isSealed

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Update method and interface implementation
    // ---------------------------------------------------------------------------------------------------------------------------------------

    /// Invoked exactly once during each system step.
    abstract member Update : unit -> unit
    default this.Update () = ()

    interface IComponent with
        override this.Name = this.Name

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Internal access
    // ---------------------------------------------------------------------------------------------------------------------------------------

    /// Allows access to a non-public member of the component.
    member this.Access<'T> memberName =
        nullOrWhitespaceArg memberName "memberName"
        MemberAccess<'T> (this, memberName)

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Methods that can only be called during metadata initialization
    // ---------------------------------------------------------------------------------------------------------------------------------------

    /// Sets the initial values of a field of the component instance.
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

            fields.[fieldInfo.Name] <-
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
    member internal this.FinalizeMetadata (?componentName : string) =
        requiresNotSealed ()

        isSealed <- true
        name <- defaultArg componentName String.Empty

        this.GetType().GetFields(BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic)
        |> Seq.where (fun field -> not <| typeof<IComponent>.IsAssignableFrom(field.FieldType) && not <| fields.ContainsKey(field.Name))
        |> Seq.iter (fun field ->
            let value =
                if field.FieldType.IsEnum then
                    (field.GetValue(this) :?> IConvertible).ToInt32 (CultureInfo.InvariantCulture) :> obj
                else
                    field.GetValue this
            fields.Add (field.Name, [value])
        )

        let subcomponentMetadata = 
            this.GetType().GetFields(BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic)
            |> Seq.where (fun field -> typeof<IComponent>.IsAssignableFrom(field.FieldType))
            |> Seq.map (fun field -> (field, field.GetValue(this)))
            |> Seq.where (fun (field, component') -> component' <> null)
            |> Seq.map (fun (field, component') -> (field, component' :?> Component))
            |> List.ofSeq

        subcomponents <- subcomponentMetadata |> List.map snd
        subcomponentMetadata
        |> List.iter (fun (field, component') -> 
            // Make sure that we won't finalize the same component twice (might happen when components are shared, will be detected later)
            if not component'.IsMetadataFinalized then
                component'.FinalizeMetadata (sprintf "%s.%s" name field.Name)
        )

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // Methods that can only be called after metadata initialization
    // ---------------------------------------------------------------------------------------------------------------------------------------

    /// Gets the initial values of the field with name <paramref name="fieldName" />.
    member internal this.GetInitialValuesOfField fieldName =
        nullOrWhitespaceArg fieldName "fieldName"
        requiresIsSealed ()

        let (result, initialValues) = fields.TryGetValue fieldName
        invalidArg (not result) "fieldName" "A field with name '%s' does not exist." fieldName

        initialValues

    /// <summary>
    /// Gets the subcomponent with the given name.
    /// </summary>
    member internal this.GetSubcomponent subcomponentName =
        nullOrWhitespaceArg subcomponentName "subcomponentName"
        requiresIsSealed ()

        let subcomponent = subcomponents |> List.tryFind (fun component' -> component'.Name.EndsWith subcomponentName)
        match subcomponent with
        | Some subcomponent -> subcomponent
        | None ->
            invalidArg true "subcomponentName" "A subcomponent with name '%s' does not exist." subcomponentName
            subcomponent.Value // Required, but cannot be reached

    /// Gets the name of the component instance. Returns the empty string if no component name could be determined.
    member internal this.Name
        with get () : string = 
            requiresIsSealed ()
            name

    /// Gets the <see cref="Component" /> instances that are direct subcomponents of the current instance.
    member internal this.Subcomponents 
        with get () = 
            requiresIsSealed ()
            subcomponents