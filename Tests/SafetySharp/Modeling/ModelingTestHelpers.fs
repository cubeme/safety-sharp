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

namespace Modeling

open System
open System.Linq
open System.Linq.Expressions
open System.Reflection
open SafetySharp
open SafetySharp.Runtime.Modeling
open SafetySharp.Runtime.Modeling

[<AutoOpen>]
module Helpers =
    /// Gets the name of the CLR field generated by the F# compiler for an explicit val declaration with the given name.
    let fsharpFieldName = sprintf "%s@"

    /// Gets the name of the CLR field generated by the F# compiler for an explicit val declaration with the given name.
    let fsharpSubcomponentName = sprintf "%s@@%d" 

    /// Creates a Linq expression that accesses the field with the given name within the component instance.
    let createTypedFieldExpression<'T> (o : obj) field (typeInfo : Type) = 
        let fieldInfo = typeInfo.GetField(fsharpFieldName field, BindingFlags.NonPublic ||| BindingFlags.Instance)
        if fieldInfo = null then invalidOp "Unable to find field '%s' in '%s'." field (typeInfo.FullName)
        Expression.Lambda<Func<'T>>(Expression.MakeMemberAccess(Expression.Constant(o), fieldInfo))

    /// Creates a Linq expression that accesses the field with the given name within the component instance.
    let createFieldExpression<'T> (o : obj) field = 
        createTypedFieldExpression<'T> o field (o.GetType ())

type internal EmptyComponent () =
    inherit Component ()

type internal OneFieldComponent =
    inherit Component

    new () = { _field = 0 }
    val private _field : int

type internal TwoFieldsComponent =
    inherit Component

    new () = { _field1 = 0; _field2 = false }
    val private _field1 : int
    val private _field2 : bool

type internal GenericComponent<'T> =
    inherit Component 

    new () = { _field = Unchecked.defaultof<'T> }
    val private _field : 'T

type internal FieldComponent<'T> =
    inherit Component 
    
    val private _field : 'T

    new () = { _field = Unchecked.defaultof<'T> }

    new (value : 'T) as this = { _field = Unchecked.defaultof<'T> } then
        this.SetInitialValues (createTypedFieldExpression<'T> this "_field" typeof<FieldComponent<'T>>, value)

    new (value1 : 'T, value2 : 'T) as this = { _field = Unchecked.defaultof<'T> } then
        this.SetInitialValues (createTypedFieldExpression<'T> this "_field" typeof<FieldComponent<'T>>, value1, value2)

    member this.Field = this._field

type internal InheritedComponent =
    inherit FieldComponent<int>
    val private _otherField : int

    new () = { inherit FieldComponent<int> 0; _otherField = 0 }
    new (field, otherField) = { inherit FieldComponent<int> (field); _otherField = otherField }

    member this.OtherField = this._otherField

type internal FieldComponent<'T1, 'T2> =
    inherit Component 
    
    val private _field1 : 'T1
    val private _field2 : 'T2

    new () = { _field1 = Unchecked.defaultof<'T1>; _field2 = Unchecked.defaultof<'T2> }

    new (value1 : 'T1, value2 : 'T2) as this = 
        { _field1 = Unchecked.defaultof<'T1>; _field2 = Unchecked.defaultof<'T2> } then
        this.SetInitialValues (createFieldExpression<'T1> this "_field1", value1)
        this.SetInitialValues (createFieldExpression<'T2> this "_field2", value2)

    new (value1a : 'T1, value1b : 'T1, value2a : 'T2, value2b : 'T2) as this = 
        { _field1 = Unchecked.defaultof<'T1>; _field2 = Unchecked.defaultof<'T2> } then
        this.SetInitialValues (createFieldExpression<'T1> this "_field1", value1a, value1b)
        this.SetInitialValues (createFieldExpression<'T2> this "_field2", value2a, value2b)
        
type internal OneSubcomponent =
    inherit Component

    val _component : Component

    new () = { _component = Unchecked.defaultof<Component> }
    new component' = { _component = component' }

type internal SelfSubcomponent =
    inherit Component

    val mutable _component : Component

    new () as this = { _component = null } then this._component <- this

type internal TwoSubcomponents =
    inherit Component

    val _component1 : Component
    val _component2 : Component

    new (component1, component2) = { _component1 = component1; _component2 = component2 }

type internal ComplexComponent =
    inherit Component

    val _nested1 : Component
    val _nested2 : Component
    val _other : obj

    new (nested1, nested2, other) =
        { _nested1 = nested1; _nested2 = nested2; _other = other }

type internal ProvidedComponent () =
    inherit Component ()

    [<Provided>] member this.X (i : int) = i
    [<Provided>] member this.X (i : int byref) = i
    [<Provided>] member this.Y () = ()

type internal RequiredComponent () =
    inherit Component ()

    [<Required>] member this.X (i : int) = i
    [<Required>] member this.X (i : int byref) = i
    [<Required>] member this.Y () = ()

type internal EmptyModel () =
    inherit Model ()

type internal TestModel ([<ParamArray>] components : Component array) as this =
    inherit Model ()
    do this.SetRootComponents components