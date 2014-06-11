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

namespace SafetySharp.Tests.Modeling.ComponentTests

open System
open System.Linq
open System.Linq.Expressions
open System.Reflection
open NUnit.Framework
open Swensen.Unquote
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp
open SafetySharp.Metamodel
open SafetySharp.Modeling
open SafetySharp.Tests.CSharp

[<AutoOpen>]
module private ComponentTestsHelper =
    // This code depends on the F# compiler creating an internal field called 'fieldName@' for a 'val fieldName' expression
    let fieldName field = field + "@"

    let createExpression<'T> (component' : Component) field = 
        let fieldInfo = component'.GetType().GetField(fieldName field, BindingFlags.NonPublic ||| BindingFlags.Instance)
        if fieldInfo = null then
            sprintf "Unable to find field '%s' in '%s'." field (component'.GetType().FullName) |> invalidOp
        Expression.Lambda<Func<'T>>(Expression.MakeMemberAccess(Expression.Constant(component'), fieldInfo))

    type FieldComponent<'T> =
        inherit Component 
    
        val _field : 'T

        new () = { _field = Unchecked.defaultof<'T> }

        new (value : 'T) as this = { _field = Unchecked.defaultof<'T> } then
            this.SetInitialValues (createExpression<'T> this "_field", value)

        new (value1 : 'T, value2 : 'T) as this = { _field = Unchecked.defaultof<'T> } then
            this.SetInitialValues (createExpression<'T> this "_field", value1, value2)

    type FieldComponent<'T1, 'T2> =
        inherit Component 
    
        val _field1 : 'T1
        val _field2 : 'T2

        new () = { _field1 = Unchecked.defaultof<'T1>; _field2 = Unchecked.defaultof<'T2> }

        new (value1 : 'T1, value2 : 'T2) as this = 
            { _field1 = Unchecked.defaultof<'T1>; _field2 = Unchecked.defaultof<'T2> } then
            this.SetInitialValues (createExpression<'T1> this "_field1", value1)
            this.SetInitialValues (createExpression<'T2> this "_field2", value2)

        new (value1a : 'T1, value1b : 'T1, value2a : 'T2, value2b : 'T2) as this = 
            { _field1 = Unchecked.defaultof<'T1>; _field2 = Unchecked.defaultof<'T2> } then
            this.SetInitialValues (createExpression<'T1> this "_field1", value1a, value1b)
            this.SetInitialValues (createExpression<'T2> this "_field2", value2a, value2b)
        
    type OneSubcomponent =
        inherit Component

        val _component : Component

        new () = { _component = Unchecked.defaultof<Component> }
        new component' = { _component = component' }

    type TwoSubcomponents =
        inherit Component

        val _component1 : Component
        val _component2 : Component

        new (component1, component2) = { _component1 = component1; _component2 = component2 }

[<TestFixture>]
module ``SetInitialValues method`` =
    [<Test>]
    let ``sets field value`` () =
        let component' = new FieldComponent<int>(3)
        component'._field =? 3

        let component' = new FieldComponent<int>(3, 182)
        (component'._field = 3 || component'._field = 182) =? true

    [<Test>]
    let ``throws when field expression is null`` () =
        let component' = new FieldComponent<int>()
        raises<ArgumentNullException> <@ component'.SetInitialValues (null, 1, 2) @>

    [<Test>]
    let ``throws when initial values is null`` () =
        let component' = new FieldComponent<int>()
        raises<ArgumentNullException> <@ component'.SetInitialValues (createExpression<int> component' "_field", null) @>

    [<Test>]
    let ``throws when initial values is empty`` () =
        let component' = new FieldComponent<int>()
        raises<ArgumentException> <@ component'.SetInitialValues (createExpression<int> component' "_field") @>

[<TestFixture>]
module ``GetInitialValuesOfField method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        let component' = FieldComponent<int> 3
        component'.FinalizeMetadata ()

        raises<ArgumentException> <@ component'.GetInitialValuesOfField null @>

    [<Test>]
    let ``throws when empty string is passed`` () =
        let component' = FieldComponent<int> 3
        component'.FinalizeMetadata ()

        raises<ArgumentException> <@ component'.GetInitialValuesOfField "" @>

    [<Test>]
    let ``throws for unknown field`` () =
        let component' = FieldComponent<int> 3
        component'.FinalizeMetadata ()

        raises<ArgumentException> <@ component'.GetInitialValuesOfField "abcd" @>

    [<Test>]
    let ``throws when metadata has not been finalized`` () =
        let component' = FieldComponent<int> 3
        raises<InvalidOperationException> <@ component'.GetInitialValuesOfField <| fieldName "_field" @>

    [<Test>]
    let ``throws for subcomponent field`` () =
        let component' = OneSubcomponent (FieldComponent<int> 3)
        component'.FinalizeMetadata ()

        raises<ArgumentException> <@ component'.GetInitialValuesOfField <| fieldName "_component" @>

    [<Test>]
    let ``returns initial value of single field`` () =
        let integerComponent = new FieldComponent<int> 17
        integerComponent.FinalizeMetadata ()
        integerComponent.GetInitialValuesOfField(fieldName "_field") =? [17]
    
        let integerComponent = new FieldComponent<int> ()
        integerComponent.FinalizeMetadata ()
        integerComponent.GetInitialValuesOfField(fieldName "_field") =? [0]
    
        let booleanComponent = new FieldComponent<bool> true
        booleanComponent.FinalizeMetadata ()
        booleanComponent.GetInitialValuesOfField(fieldName "_field") =? [true]
    
        let booleanComponent = new FieldComponent<bool> ()
        booleanComponent.FinalizeMetadata ()
        booleanComponent.GetInitialValuesOfField(fieldName "_field") =? [false]

    [<Test>]
    let ``returns initial value of multiple fields`` () =
        let component' = new FieldComponent<int, bool> (33, true)
        component'.FinalizeMetadata ()
        
        component'.GetInitialValuesOfField(fieldName "_field1") =? [33]
        component'.GetInitialValuesOfField(fieldName "_field2") =? [true]
        
        let component' = new FieldComponent<int, bool> ()
        component'.FinalizeMetadata ()
        
        component'.GetInitialValuesOfField(fieldName "_field1") =? [0]
        component'.GetInitialValuesOfField(fieldName "_field2") =? [false]

    [<Test>]
    let ``returns nondeterministic initial values of single field`` () =
        let integerComponent = new FieldComponent<int>(17)
        integerComponent.FinalizeMetadata ()
        integerComponent.GetInitialValuesOfField(fieldName "_field") =? [17]

        let integerComponent = new FieldComponent<int>(17, 33)
        integerComponent.FinalizeMetadata ()
        integerComponent.GetInitialValuesOfField(fieldName "_field") =? [17; 33]

        let booleanComponent = new FieldComponent<bool>(true)
        booleanComponent.FinalizeMetadata ()
        booleanComponent.GetInitialValuesOfField(fieldName "_field") =? [true]

        let booleanComponent = new FieldComponent<bool>(true, false)
        booleanComponent.FinalizeMetadata ()
        booleanComponent.GetInitialValuesOfField(fieldName "_field") =? [true; false]
        
    [<Test>]
    let ``returns nondeterministic initial values of multiple fields`` () =
        let component' = new FieldComponent<int, bool>(158, 392, false, true)
        component'.FinalizeMetadata ()

        component'.GetInitialValuesOfField(fieldName "_field1") =? [158; 392]
        component'.GetInitialValuesOfField(fieldName "_field2") =? [false; true]

[<TestFixture>]
module ``GetSubcomponent method`` = 
    [<Test>]
    let ``throws when null is passed`` () =
        let component' = new FieldComponent<int> ()
        component'.FinalizeMetadata ()

        raises<ArgumentException> <@ component'.GetSubcomponent null @>

    [<Test>]
    let ``throws when empty string is passed`` () =
        let component' = new FieldComponent<int> ()
        component'.FinalizeMetadata ()

        raises<ArgumentException> <@ component'.GetSubcomponent "" @>

    [<Test>]
    let ``throws when metadata has not been finalized`` () =
        let component' = new FieldComponent<int> ()
        raises<InvalidOperationException> <@ component'.GetSubcomponent (fieldName "_field") @>

    [<Test>]
    let ``throws for non-component field`` () =
        let component' = new FieldComponent<int> ()
        component'.FinalizeMetadata ()

        raises<ArgumentException> <@ component'.GetSubcomponent (fieldName "_field") @>

    [<Test>]
    let ``throws for unknown field`` () =
        let component' = new FieldComponent<int> ()
        component'.FinalizeMetadata ()

        raises<ArgumentException> <@ component'.GetSubcomponent (fieldName "abcd") @>

    [<Test>]
    let ``returns single subcomponent`` () =
        let subcomponent = new FieldComponent<int> ()
        let component' = new OneSubcomponent (subcomponent)
        component'.FinalizeMetadata ()

        component'.GetSubcomponent (fieldName "_component") =? (subcomponent :> Component)

    [<Test>]
    let ``returns multiple subcomponents`` () =
        let subcomponent1 = new FieldComponent<int> ()
        let subcomponent2 = new FieldComponent<bool> ()
        let component' = new TwoSubcomponents (subcomponent1, subcomponent2)
        component'.FinalizeMetadata ()

        component'.GetSubcomponent(fieldName "_component1") =? (subcomponent1 :> Component)
        component'.GetSubcomponent(fieldName "_component2") =? (subcomponent2 :> Component)

[<TestFixture>]
module ``Subcomponents property`` =
    [<Test>]
    let ``throws when metadata has not been finalized`` () =
        let component' = new OneSubcomponent (new FieldComponent<int> 3)
        raises<InvalidOperationException> <@ component'.Subcomponents @>

    [<Test>]
    let ``ignores non-component fields`` () =
        let component' = new FieldComponent<int> 3
        component'.FinalizeMetadata ()

        component'.Subcomponents =? []

    [<Test>]
    let ``ignores null subcomponents`` () =
        let component' = new OneSubcomponent ()
        component'.FinalizeMetadata ()

        component'.Subcomponents =? []

    [<Test>]
    let ``is empty when component has no subcomponents`` () =
        let component' = { new Component () with member this.Update () = () }
        component'.FinalizeMetadata ()

        component'.Subcomponents =? []

    [<Test>]
    let ``contains single subcomponent`` () =
        let subcomponent = new FieldComponent<int> 3
        let component' = new OneSubcomponent (subcomponent)
        component'.FinalizeMetadata ()

        component'.Subcomponents =? [subcomponent]

    [<Test>]
    let ``contains multiple subcomponents`` () =
        let subcomponent1 = new FieldComponent<int> 3
        let subcomponent2 = new FieldComponent<bool> true
        let component' = new TwoSubcomponents (subcomponent1, subcomponent2)
        component'.FinalizeMetadata ()

        component'.Subcomponents =? [subcomponent1; subcomponent2]

    [<Test>]
    let ``contains named subcomponents`` () =
        let subcomponent1 = new FieldComponent<int> 3
        let subcomponent2 = new FieldComponent<bool> true
        let component' = new TwoSubcomponents (subcomponent1, subcomponent2)
        component'.FinalizeMetadata ()

        component'.Subcomponents.[0].Name =? fieldName "_component1"
        component'.Subcomponents.[1].Name =? fieldName "_component2"