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
open SafetySharp.Modeling
open SafetySharp.Tests

type private TestEnum =
    | Default = 0
    | A = 1
    | B = 2

[<TestFixture>]
module ``SetInitialValues method`` =
    [<Test>]
    let ``sets the value of field declared by the component`` () =
        let component' = FieldComponent<int> 3
        component'.Field =? 3

        let component' = FieldComponent<int> (3, 182)
        (component'.Field = 3 || component'.Field = 182) =? true

    [<Test>]
    let ``sets the value of inherited and non-inherited fields`` () =
        let component' = InheritedComponent ()
        component'.SetInitialValues (createFieldExpression<int> component' "_field", 51)
        component'.SetInitialValues (createFieldExpression<int> component' "_otherField", 122)

        component'.Field =? 51
        component'.OtherField =? 122

    [<Test>]
    let ``throws when field expression is null`` () =
        let component' = FieldComponent<int>()
        raisesArgumentNullException "field" (fun () -> component'.SetInitialValues (null, 1, 2) |> ignore)

    [<Test>]
    let ``throws when initial values is null`` () =
        let component' = FieldComponent<int>()
        let field = createFieldExpression<int> component' "_field"
        raisesArgumentNullException "initialValues" (fun () -> component'.SetInitialValues (field, (null : int array)) |> ignore)

    [<Test>]
    let ``throws when initial values is empty`` () =
        let component' = FieldComponent<int>()
        let field = createFieldExpression<int> component' "_field"
        let values : int array = [||]
        raisesArgumentException "initialValues" (fun () -> component'.SetInitialValues (field, values) |> ignore)

    [<Test>]
    let ``throws when the component metadata has already been finalized`` () =
        let component' = FieldComponent<int> ()
        component'.FinalizeMetadata ()

        raises<InvalidOperationException> (fun () -> component'.SetInitialValues (createFieldExpression<int> component' "_field", 1) |> ignore)

    [<Test>]
    let ``throws when field does not reference a field of the component`` () =
        let component' = InheritedComponent ()
        let otherComponent = FieldComponent<int, int> ()

        raisesArgumentException "field" (fun () -> component'.SetInitialValues (createFieldExpression<int> otherComponent "_field1", 17)  |> ignore)

    [<Test>]
    let ``throws when undefined enum value is passed`` () =
        let component' = FieldComponent<TestEnum> ()
        raisesArgumentException "initialValues" (fun () -> component'.SetInitialValues (createFieldExpression<TestEnum> component' "_field", enum<TestEnum> 177) |> ignore)

[<TestFixture>]
module ``FinalizeMetadata method`` =
    [<Test>]
    let ``throws when the metadata has already been finalized`` () =
        let component' = EmptyComponent ()
        component'.FinalizeMetadata ()

        raises<InvalidOperationException> (fun () -> component'.FinalizeMetadata () |> ignore)

    [<Test>]
    let ``updates the IsMetadataFinalized property`` () =
        let component' = EmptyComponent ()
        component'.IsMetadataFinalized =? false

        component'.FinalizeMetadata ()
        component'.IsMetadataFinalized =? true

[<TestFixture>]
module ``GetInitialValuesOfField method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        let component' = FieldComponent<int> 3
        component'.FinalizeMetadata ()

        raisesArgumentNullException "fieldName" (fun () -> component'.GetInitialValuesOfField null |> ignore)

    [<Test>]
    let ``throws when empty string is passed`` () =
        let component' = FieldComponent<int> 3
        component'.FinalizeMetadata ()

        raisesArgumentException "fieldName" (fun () -> component'.GetInitialValuesOfField "" |> ignore)

    [<Test>]
    let ``throws for unknown field`` () =
        let component' = FieldComponent<int> 3
        component'.FinalizeMetadata ()

        raisesArgumentException "fieldName" (fun () -> component'.GetInitialValuesOfField "abcd" |> ignore)

    [<Test>]
    let ``throws when metadata has not yet been finalized`` () =
        let component' = FieldComponent<int> 3
        raises<InvalidOperationException> (fun () -> component'.GetInitialValuesOfField <| fsharpFieldName "_field" |> ignore)

    [<Test>]
    let ``throws for subcomponent field`` () =
        let component' = OneSubcomponent (FieldComponent<int> 3)
        component'.FinalizeMetadata ()

        raisesArgumentException "fieldName" (fun () -> component'.GetInitialValuesOfField <| fsharpFieldName "_component" |> ignore)

    [<Test>]
    let ``returns initial value of single field`` () =
        let integerComponent = FieldComponent<int> 17
        integerComponent.FinalizeMetadata ()
        integerComponent.GetInitialValuesOfField (fsharpFieldName "_field") =? [17]
    
        let integerComponent = FieldComponent<int> ()
        integerComponent.FinalizeMetadata ()
        integerComponent.GetInitialValuesOfField (fsharpFieldName "_field") =? [0]
    
        let booleanComponent = FieldComponent<bool> true
        booleanComponent.FinalizeMetadata ()
        booleanComponent.GetInitialValuesOfField (fsharpFieldName "_field") =? [true]
    
        let booleanComponent = FieldComponent<bool> ()
        booleanComponent.FinalizeMetadata ()
        booleanComponent.GetInitialValuesOfField (fsharpFieldName "_field") =? [false]

    [<Test>]
    let ``returns initial value of multiple fields`` () =
        let component' = FieldComponent<int, bool> (33, true)
        component'.FinalizeMetadata ()
        
        component'.GetInitialValuesOfField (fsharpFieldName "_field1") =? [33]
        component'.GetInitialValuesOfField (fsharpFieldName "_field2") =? [true]
        
        let component' = FieldComponent<int, bool> ()
        component'.FinalizeMetadata ()
        
        component'.GetInitialValuesOfField (fsharpFieldName "_field1") =? [0]
        component'.GetInitialValuesOfField (fsharpFieldName "_field2") =? [false]

    [<Test>]
    let ``returns nondeterministic initial values of single field`` () =
        let integerComponent = FieldComponent<int>(17)
        integerComponent.FinalizeMetadata ()
        integerComponent.GetInitialValuesOfField (fsharpFieldName "_field") =? [17]

        let integerComponent = FieldComponent<int>(17, 33)
        integerComponent.FinalizeMetadata ()
        integerComponent.GetInitialValuesOfField (fsharpFieldName "_field") =? [17; 33]

        let booleanComponent = FieldComponent<bool>(true)
        booleanComponent.FinalizeMetadata ()
        booleanComponent.GetInitialValuesOfField (fsharpFieldName "_field") =? [true]

        let booleanComponent = FieldComponent<bool>(true, false)
        booleanComponent.FinalizeMetadata ()
        booleanComponent.GetInitialValuesOfField (fsharpFieldName "_field") =? [true; false]
        
    [<Test>]
    let ``returns nondeterministic initial values of multiple fields`` () =
        let component' = FieldComponent<int, bool>(158, 392, false, true)
        component'.FinalizeMetadata ()

        component'.GetInitialValuesOfField (fsharpFieldName "_field1") =? [158; 392]
        component'.GetInitialValuesOfField (fsharpFieldName "_field2") =? [false; true]

    [<Test>]
    let ``returns integer values for fields of enumeration type`` () =
        let component' = FieldComponent<TestEnum> ()
        component'.FinalizeMetadata ()
        component'.GetInitialValuesOfField (fsharpFieldName "_field") =? [0]

        let component' = FieldComponent<TestEnum> (TestEnum.A, TestEnum.B)
        component'.FinalizeMetadata ()
        component'.GetInitialValuesOfField (fsharpFieldName "_field") =? [1; 2]

    [<Test>]
    let ``returns latest initial values when previous initial values were overridden`` () =
        let component' = FieldComponent<int> (1, 2)
        component'.SetInitialValues (createFieldExpression component' "_field", 17)
        component'.FinalizeMetadata ()
        component'.GetInitialValuesOfField (fsharpFieldName "_field") =? [17]
        
        let component' = FieldComponent<int> (17)
        component'.SetInitialValues (createFieldExpression component' "_field", 17, 93, 1)
        component'.FinalizeMetadata ()
        component'.GetInitialValuesOfField (fsharpFieldName "_field") =? [17; 93; 1]

[<TestFixture>]
module ``GetSubcomponent method`` = 
    [<Test>]
    let ``throws when null is passed`` () =
        let component' = FieldComponent<int> ()
        component'.FinalizeMetadata ()

        raisesArgumentNullException "subcomponentName" (fun () -> component'.GetSubcomponent null |> ignore)

    [<Test>]
    let ``throws when empty string is passed`` () =
        let component' = FieldComponent<int> ()
        component'.FinalizeMetadata ()

        raisesArgumentException "subcomponentName" (fun () -> component'.GetSubcomponent "" |> ignore)

    [<Test>]
    let ``throws when metadata has not yet been finalized`` () =
        let component' = FieldComponent<int> ()
        raises<InvalidOperationException> (fun () -> component'.GetSubcomponent (fsharpFieldName "_field") |> ignore)

    [<Test>]
    let ``throws for non-component field`` () =
        let component' = FieldComponent<int> ()
        component'.FinalizeMetadata ()

        raisesArgumentException "subcomponentName" (fun () -> component'.GetSubcomponent (fsharpFieldName "_field") |> ignore)

    [<Test>]
    let ``throws for unknown field`` () =
        let component' = FieldComponent<int> ()
        component'.FinalizeMetadata ()

        raisesArgumentException "subcomponentName" (fun () -> component'.GetSubcomponent (fsharpFieldName "abcd") |> ignore)

    [<Test>]
    let ``returns single subcomponent`` () =
        let subcomponent = FieldComponent<int> ()
        let component' = OneSubcomponent (subcomponent)
        component'.FinalizeMetadata ()

        component'.GetSubcomponent (fsharpFieldName "_component") =? (subcomponent :> Component)

    [<Test>]
    let ``returns multiple subcomponents`` () =
        let subcomponent1 = FieldComponent<int> ()
        let subcomponent2 = FieldComponent<bool> ()
        let component' = TwoSubcomponents (subcomponent1, subcomponent2)
        component'.FinalizeMetadata ()

        component'.GetSubcomponent(fsharpFieldName "_component1") =? (subcomponent1 :> Component)
        component'.GetSubcomponent(fsharpFieldName "_component2") =? (subcomponent2 :> Component)

[<TestFixture>]
module ``Subcomponents property`` =
    [<Test>]
    let ``throws when metadata has not yet been finalized`` () =
        let component' = OneSubcomponent (FieldComponent<int> 3)
        raises<InvalidOperationException> (fun () -> component'.Subcomponents |> ignore)

    [<Test>]
    let ``ignores non-component fields`` () =
        let component' = FieldComponent<int> 3
        component'.FinalizeMetadata ()

        component'.Subcomponents =? []

    [<Test>]
    let ``ignores null subcomponents`` () =
        let component' = OneSubcomponent ()
        component'.FinalizeMetadata ()

        component'.Subcomponents =? []

    [<Test>]
    let ``is empty when component has no subcomponents`` () =
        let component' = EmptyComponent ()
        component'.FinalizeMetadata ()

        component'.Subcomponents =? []

    [<Test>]
    let ``contains single subcomponent`` () =
        let subcomponent = FieldComponent<int> 3
        let component' = OneSubcomponent (subcomponent)
        component'.FinalizeMetadata ()

        component'.Subcomponents =? [subcomponent]

    [<Test>]
    let ``contains multiple subcomponents`` () =
        let subcomponent1 = FieldComponent<int> 3
        let subcomponent2 = FieldComponent<bool> true
        let component' = TwoSubcomponents (subcomponent1, subcomponent2)
        component'.FinalizeMetadata ()

        component'.Subcomponents =? [subcomponent1; subcomponent2]

    [<Test>]
    let ``contains named subcomponents`` () =
        let subcomponent1 = FieldComponent<int> 3
        let subcomponent2 = FieldComponent<bool> true
        let component' = TwoSubcomponents (subcomponent1, subcomponent2)
        component'.FinalizeMetadata "Root"

        component'.Subcomponents.[0].Name =? fsharpFieldName "Root._component1"
        component'.Subcomponents.[1].Name =? fsharpFieldName "Root._component2"

// These tests assume that the F# compiler generates a property named 'x' and a backing field with
// some internal name for a 'val x : type' expression within a class.
[<TestFixture>]
module ``Access method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        let component' = EmptyComponent ()
        raisesArgumentNullException "memberName" (fun () -> component'.Access<bool> null |> ignore)

    [<Test>]
    let ``throws when empty string is passed`` () =
        let component' = EmptyComponent ()
        raisesArgumentException "memberName" (fun () -> component'.Access<bool> "" |> ignore)

    [<Test>]
    let ``throws when no member with the given name exists`` () =
        let component' = EmptyComponent ()
        raises<InvalidOperationException> (fun () -> component'.Access<bool> "xyz" |> ignore)

    [<Test>]
    let ``throws when field with given name exists but types differ`` () =
        let component' = FieldComponent<int> ()
        raises<InvalidOperationException> (fun () -> component'.Access<bool> (fsharpFieldName "_field") |> ignore)

        let component' = FieldComponent<int, bool> ()
        raises<InvalidOperationException> (fun () -> component'.Access<bool> (fsharpFieldName "_field1") |> ignore)
        raises<InvalidOperationException> (fun () -> component'.Access<int> (fsharpFieldName "_field2") |> ignore)

    [<Test>]
    let ``throws when property with given name exists but types differ`` () =
        let component' = FieldComponent<int> ()
        raises<InvalidOperationException> (fun () -> component'.Access<bool> "_field" |> ignore)

        let component' = FieldComponent<int, bool> ()
        raises<InvalidOperationException> (fun () -> component'.Access<bool> "_field1" |> ignore)
        raises<InvalidOperationException> (fun () -> component'.Access<int> "_field2" |> ignore)

    type SetterOnlyComponent () =
        inherit Component ()
        member this.X with set (value : int) = ()

    [<Test>]
    let ``throws when property has no getter`` () =
        let component' = SetterOnlyComponent ()
        raises<InvalidOperationException> (fun () -> component'.Access<int> "X" |> ignore)

    [<Test>]
    let ``gets field value when integer field with given name exists`` () =
        let component' = FieldComponent<int> 17
        component'.Access<int>(fsharpFieldName "_field").Value =? 17

    [<Test>]
    let ``gets field value when Boolean field with given name exists`` () =
        let component' = FieldComponent<bool> true
        component'.Access<bool>(fsharpFieldName "_field").Value =? true

    [<Test>]
    let ``gets field value when decimal field with given name exists`` () =
        let component' = FieldComponent<decimal> 17.4m
        component'.Access<decimal>(fsharpFieldName "_field").Value =? 17.4m

    [<Test>]
    let ``gets property value when integer field with given name exists`` () =
        let component' = FieldComponent<int> 17
        component'.Access<int>("_field").Value =? 17

    [<Test>]
    let ``gets property value when Boolean field with given name exists`` () =
        let component' = FieldComponent<bool> true
        component'.Access<bool>("_field").Value =? true

    [<Test>]
    let ``gets property value when decimal field with given name exists`` () =
        let component' = FieldComponent<decimal> 17.4m
        component'.Access<decimal>("_field").Value =? 17.4m

    [<Test>]
    let ``gets field values when component has more than one field`` () =
        let component' = FieldComponent<int, bool> (47, true)
        component'.Access<int>(fsharpFieldName "_field1").Value =? 47
        component'.Access<bool>(fsharpFieldName  "_field2").Value =? true

    [<Test>]
    let ``gets property values when component has more than one property`` () =
        let component' = FieldComponent<int, bool> (47, true)
        component'.Access<int>("_field1").Value =? 47
        component'.Access<bool>("_field2").Value =? true

    [<Test>]
    let ``gets value of public property`` () =
        let component' = FieldComponent<decimal> 17.4m
        component'.Access<decimal>("Field").Value =? 17.4m

    [<Test>]
    let ``gets value of inherited and non-inherited fields and properties`` () =
        let component' = InheritedComponent (44, 15)
        component'.Access<int>(fsharpFieldName "_field").Value =? 44
        component'.Access<int>(fsharpFieldName "_otherField").Value =? 15
        component'.Access<int>("_field").Value =? 44
        component'.Access<int>("_otherField").Value =? 15