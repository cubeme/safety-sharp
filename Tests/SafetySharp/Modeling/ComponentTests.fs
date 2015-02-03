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

namespace Modeling.``Component Tests``

open System
open System.Linq
open System.Linq.Expressions
open System.Reflection
open NUnit.Framework
open Modeling
open SafetySharp
open SafetySharp.Modeling
open Mono.Cecil

type private TestEnum =
    | Default = 0
    | A = 1
    | B = 2

[<TestFixture>]
module ``SetInitialValues method`` =
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

        raisesInvalidOpException (fun () -> component'.SetInitialValues (createFieldExpression<int> component' "_field", 1) |> ignore)

    [<Test>]
    let ``throws when field is constant`` () =
        // Compile a C# class, as F# does not support IL constant fields
        raisesArgumentException "field" (fun () -> unwrap<TargetInvocationException> (fun () ->  TestCompilation.CreateModel "class TestModel : Model { public TestModel() { SetRootComponents(new C()); }} class C : Component { const int x = 4; public C() { SetInitialValues(() => x, 1, 2, 3); }}" |> ignore))

    [<Test>]
    let ``throws when field does not reference a field of the component`` () =
        let component' = InheritedComponent ()
        let otherComponent = FieldComponent<int, int> ()

        raisesArgumentException "field" (fun () -> component'.SetInitialValues (createFieldExpression<int> otherComponent "_field1", 17)  |> ignore)

    [<Test>]
    let ``throws when undefined enum value is passed`` () =
        let component' = FieldComponent<TestEnum> ()
        raisesArgumentException "initialValues" (fun () -> component'.SetInitialValues (createFieldExpression<TestEnum> component' "_field", enum<TestEnum> 177) |> ignore)

    [<Test>]
    let ``does not throw when initial values are set multiple times for the same field`` () =
        let component' = FieldComponent<int> ()
        component'.SetInitialValues (createFieldExpression<int> component' "_field", 1, 2, 3)
        nothrow (fun () -> component'.SetInitialValues (createFieldExpression<int> component' "_field", 1, 3))

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

[<TestFixture>]
module ``FinalizeMetadata method`` =
    [<Test>]
    let ``throws when the metadata has already been finalized`` () =
        let component' = EmptyComponent ()
        component'.FinalizeMetadata ()

        raisesInvalidOpException (fun () -> component'.FinalizeMetadata () |> ignore)

    [<Test>]
    let ``updates the IsMetadataFinalized property`` () =
        let component' = EmptyComponent ()
        component'.IsMetadataFinalized =? false

        component'.FinalizeMetadata ()
        component'.IsMetadataFinalized =? true

[<TestFixture>]
module ``GetInitialValuesOfField method`` =
    let private getFieldDef field (declaringType : Type) = 
        let fieldInfo = declaringType.GetField(field, BindingFlags.NonPublic ||| BindingFlags.Instance)
        if fieldInfo = null then invalidOp "Unable to find field '%s' in '%s'." field (declaringType.FullName)
        let assemblyDef = AssemblyDefinition.ReadAssembly (declaringType.Assembly.Location)
        let fieldDef = (assemblyDef.MainModule.Import fieldInfo).Resolve ()
        if fieldDef = null then invalidOp "Unable to find field '%s' in '%s' in assembly metadata." field (declaringType.FullName)
        fieldDef

    let private getTypedInitialValues (component' : Component) field (declaringType : Type) =
        let fieldDef = getFieldDef field declaringType
        component'.GetInitialValuesOfField fieldDef

    let private getInitialValues component' field =
        getTypedInitialValues component' (fsharpFieldName field) (component'.GetType ())

    [<Test>]
    let ``throws when null is passed`` () =
        let component' = FieldComponent<int> 3
        component'.FinalizeMetadata ()

        raisesArgumentNullException "field" (fun () -> component'.GetInitialValuesOfField null |> ignore)

    [<Test>]
    let ``throws for unknown field`` () =
        let component' = FieldComponent<int> 3
        component'.FinalizeMetadata ()

        let unknownField = getFieldDef (fsharpFieldName "_field1") typeof<FieldComponent<int, bool>>
        raisesArgumentException "field" (fun () -> component'.GetInitialValuesOfField unknownField |> ignore)

    [<Test>]
    let ``throws when metadata has not yet been finalized`` () =
        let component' = FieldComponent<int> 3
        raisesInvalidOpException (fun () -> getInitialValues component' "_field" |> ignore)

    [<Test>]
    let ``throws for subcomponent field`` () =
        let component' = OneSubcomponent (FieldComponent<int> 3)
        component'.FinalizeMetadata ()

        raisesArgumentException "field" (fun () -> getInitialValues component' "_component" |> ignore)

    [<Test>]
    let ``returns initial value of single field`` () =
        let integerComponent = FieldComponent<int> 17
        integerComponent.FinalizeMetadata ()
        getInitialValues integerComponent "_field" =? [17]
    
        let integerComponent = FieldComponent<int> ()
        integerComponent.FinalizeMetadata ()
        getInitialValues integerComponent "_field" =? [0]
    
        let booleanComponent = FieldComponent<bool> true
        booleanComponent.FinalizeMetadata ()
        getInitialValues booleanComponent "_field" =? [true]
    
        let booleanComponent = FieldComponent<bool> ()
        booleanComponent.FinalizeMetadata ()
        getInitialValues booleanComponent "_field" =? [false]

    [<Test>]
    let ``returns initial value of multiple fields`` () =
        let component' = FieldComponent<int, bool> (33, true)
        component'.FinalizeMetadata ()
        
        getInitialValues component' "_field1" =? [33]
        getInitialValues component' "_field2" =? [true]
        
        let component' = FieldComponent<int, bool> ()
        component'.FinalizeMetadata ()
        
        getInitialValues component' "_field1" =? [0]
        getInitialValues component' "_field2" =? [false]

    [<Test>]
    let ``returns nondeterministic initial values of single field`` () =
        let integerComponent = FieldComponent<int>(17)
        integerComponent.FinalizeMetadata ()
        getInitialValues integerComponent "_field" =? [17]

        let integerComponent = FieldComponent<int>(17, 33)
        integerComponent.FinalizeMetadata ()
        getInitialValues integerComponent "_field" =? [17; 33]

        let booleanComponent = FieldComponent<bool>(true)
        booleanComponent.FinalizeMetadata ()
        getInitialValues booleanComponent "_field" =? [true]

        let booleanComponent = FieldComponent<bool>(true, false)
        booleanComponent.FinalizeMetadata ()
        getInitialValues booleanComponent "_field" =? [true; false]
        
    [<Test>]
    let ``returns nondeterministic initial values of multiple fields`` () =
        let component' = FieldComponent<int, bool>(158, 392, false, true)
        component'.FinalizeMetadata ()

        getInitialValues component' "_field1" =? [158; 392]
        getInitialValues component' "_field2" =? [false; true]

    [<Test>]
    let ``returns integer values for fields of enumeration type`` () =
        let component' = FieldComponent<TestEnum> ()
        component'.FinalizeMetadata ()
        getInitialValues component' "_field" =? [0]

        let component' = FieldComponent<TestEnum> (TestEnum.A, TestEnum.B)
        component'.FinalizeMetadata ()
        getInitialValues component' "_field" =? [1; 2]

    [<Test>]
    let ``returns latest initial values when previous initial values were overridden`` () =
        let component' = FieldComponent<int> (1, 2)
        component'.SetInitialValues (createFieldExpression component' "_field", 17)
        component'.FinalizeMetadata ()
        getInitialValues component' "_field" =? [17]
        
        let component' = FieldComponent<int> (17)
        component'.SetInitialValues (createFieldExpression component' "_field", 17, 93, 1)
        component'.FinalizeMetadata ()
        getInitialValues component' "_field" =? [17; 93; 1]

    [<Test>]
    let ``gets the latest value when initial values have been set multiple times`` () =
        let component' = FieldComponent<int> ()
        component'.SetInitialValues (createFieldExpression<int> component' "_field", 1, 2, 3)
        component'.SetInitialValues (createFieldExpression<int> component' "_field", 44, -20)
        component'.FinalizeMetadata ()
        getInitialValues component' "_field" =? [44; -20]

    [<Test>]
    let ``gets the value of inherited and non-inherited fields with conflicting names with SetInitialValues called`` () =
        let csharpCode = "class X : Component { int f; public X() { SetInitialValues(() => f, 1, 2, 3); } } class Y : X { bool f; public Y() { SetInitialValues(() => f, false, true); } }"
        let compilation = TestCompilation csharpCode
        let assembly = compilation.Compile ()
        let baseType = assembly.GetType "X"
        let derivedType = assembly.GetType "Y"
        let component' = Activator.CreateInstance derivedType :?> Component
        component'.FinalizeMetadata ()
        getTypedInitialValues component' "f" baseType =? [1; 2; 3]
        getTypedInitialValues component' "f" derivedType =? [false; true]

    [<Test>]
    let ``gets the value of inherited and non-inherited fields with conflicting names without SetInitialValues called`` () =
        let csharpCode = "class X : Component { int f; } class Y : X { bool f; }"
        let compilation = TestCompilation csharpCode
        let assembly = compilation.Compile ()
        let baseType = assembly.GetType "X"
        let derivedType = assembly.GetType "Y"
        let component' = Activator.CreateInstance derivedType :?> Component
        component'.FinalizeMetadata ()
        getTypedInitialValues component' "f" baseType =? [0]
        getTypedInitialValues component' "f" derivedType =? [false]

[<TestFixture>]
module ``RequiredPortInfo property`` =
    [<Test>]
    let ``throws when metadata has not yet been finalized`` () =
        let component' = OneSubcomponent (FieldComponent<int> 3)
        raisesInvalidOpException (fun () -> component'.RequiredPortInfo |> ignore)

    [<Test>]
    let ``returns empty list for component without required ports`` () =
        let component' = EmptyComponent ()
        component'.FinalizeMetadata ()

        component'.RequiredPortInfo =? []

    [<Test>]
    let ``ignores provided ports`` () =
        let component' = ProvidedComponent ()
        component'.FinalizeMetadata ()

        component'.RequiredPortInfo =? []

    [<Test>]
    let ``returns required ports`` () =
        let component' = RequiredComponent ()
        component'.FinalizeMetadata ()

        component'.RequiredPortInfo.Length =? 3
        component'.RequiredPortInfo.[0].Name =? "X"
        component'.RequiredPortInfo.[0].ReturnType.FullName =? "System.Int32"
        component'.RequiredPortInfo.[0].GetParameters().Length =? 1
        component'.RequiredPortInfo.[0].GetParameters().[0].ParameterType.FullName =? "System.Int32"
        component'.RequiredPortInfo.[0].GetParameters().[0].ParameterType.IsByRef =? false
        component'.RequiredPortInfo.[1].Name =? "X"
        component'.RequiredPortInfo.[1].ReturnType.FullName =? "System.Int32"
        component'.RequiredPortInfo.[1].GetParameters().Length =? 1
        component'.RequiredPortInfo.[1].GetParameters().[0].ParameterType.FullName =? "System.Int32&"
        component'.RequiredPortInfo.[1].GetParameters().[0].ParameterType.IsByRef =? true
        component'.RequiredPortInfo.[2].Name =? "Y"
        component'.RequiredPortInfo.[2].ReturnType.FullName =? "System.Void"
        component'.RequiredPortInfo.[2].GetParameters().Length =? 0

    [<Test>]
    let ``returns inherited private required ports`` () =
        let csharpCode = "class X : Component { [Required] void M() {} } class Y : X { [Required] int M() { return 0; } }"
        let compilation = TestCompilation csharpCode
        let assembly = compilation.Compile ()
        let baseType = assembly.GetType "X"
        let derivedType = assembly.GetType "Y"
        let component' = Activator.CreateInstance derivedType :?> Component
        component'.FinalizeMetadata ()

        component'.RequiredPortInfo.Length =? 2
        component'.RequiredPortInfo.[0].DeclaringType =? baseType
        component'.RequiredPortInfo.[0].Name =? "M"
        component'.RequiredPortInfo.[0].ReturnType.FullName =? "System.Void"
        component'.RequiredPortInfo.[1].DeclaringType =? derivedType
        component'.RequiredPortInfo.[1].Name =? "M"
        component'.RequiredPortInfo.[1].ReturnType.FullName =? "System.Int32"

[<TestFixture>]
module ``ProvidedPortInfo property`` =
    [<Test>]
    let ``throws when metadata has not yet been finalized`` () =
        let component' = OneSubcomponent (FieldComponent<int> 3)
        raisesInvalidOpException (fun () -> component'.ProvidedPortInfo |> ignore)

    [<Test>]
    let ``returns empty list for component without provided ports`` () =
        let component' = EmptyComponent ()
        component'.FinalizeMetadata ()

        component'.ProvidedPortInfo =? []

    [<Test>]
    let ``ignores required ports`` () =
        let component' = RequiredComponent ()
        component'.FinalizeMetadata ()

        component'.ProvidedPortInfo =? []

    [<Test>]
    let ``returns provided ports`` () =
        let component' = ProvidedComponent ()
        component'.FinalizeMetadata ()

        component'.ProvidedPortInfo.Length =? 3
        component'.ProvidedPortInfo.[0].Name =? "X"
        component'.ProvidedPortInfo.[0].ReturnType.FullName =? "System.Int32"
        component'.ProvidedPortInfo.[0].GetParameters().Length =? 1
        component'.ProvidedPortInfo.[0].GetParameters().[0].ParameterType.FullName =? "System.Int32"
        component'.ProvidedPortInfo.[0].GetParameters().[0].ParameterType.IsByRef =? false
        component'.ProvidedPortInfo.[1].Name =? "X"
        component'.ProvidedPortInfo.[1].ReturnType.FullName =? "System.Int32"
        component'.ProvidedPortInfo.[1].GetParameters().Length =? 1
        component'.ProvidedPortInfo.[1].GetParameters().[0].ParameterType.FullName =? "System.Int32&"
        component'.ProvidedPortInfo.[1].GetParameters().[0].ParameterType.IsByRef =? true
        component'.ProvidedPortInfo.[2].Name =? "Y"
        component'.ProvidedPortInfo.[2].ReturnType.FullName =? "System.Void"
        component'.ProvidedPortInfo.[2].GetParameters().Length =? 0

    [<Test>]
    let ``returns inherited private provided ports`` () =
        let csharpCode = "class X : Component { [Provided] void M() {} } class Y : X { [Provided] int M() { return 0; } }"
        let compilation = TestCompilation csharpCode
        let assembly = compilation.Compile ()
        let baseType = assembly.GetType "X"
        let derivedType = assembly.GetType "Y"
        let component' = Activator.CreateInstance derivedType :?> Component
        component'.FinalizeMetadata ()

        component'.ProvidedPortInfo.Length =? 2
        component'.ProvidedPortInfo.[0].DeclaringType =? baseType
        component'.ProvidedPortInfo.[0].Name =? "M"
        component'.ProvidedPortInfo.[0].ReturnType.FullName =? "System.Void"
        component'.ProvidedPortInfo.[1].DeclaringType =? derivedType
        component'.ProvidedPortInfo.[1].Name =? "M"
        component'.ProvidedPortInfo.[1].ReturnType.FullName =? "System.Int32"

[<TestFixture>]
module ``Bindings property`` =
    let mutable component' = (null :> Component)

    let private bindings csharpCode =
        let csharpCode = sprintf "class TestModel : Model { public TestModel() { SetRootComponents(new X()); } } %s" csharpCode
        let model = TestCompilation.CreateModel csharpCode
        model.FinalizeMetadata ()
        component' <- model.Components.[0]

    [<Test>]
    let ``throws when metadata has not yet been finalized`` () =
        let component' = OneSubcomponent (FieldComponent<int> 3)
        raisesInvalidOpException (fun () -> component'.Bindings |> ignore)

    [<Test>]
    let ``returns empty list for component without bindings`` () =
        bindings "class X : Component { void M() {} extern void N(); }"
        component'.Bindings =? []

    [<Test>]
    let ``returns delayed port binding of a component`` () =
        bindings "class X : Component { void M() {} extern void N(); public X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); } }"
        component'.Bindings.Length =? 1
        component'.Bindings.[0].Kind =? BindingKind.Delayed
        component'.Bindings.[0].Port1.IsRequiredPort =? true
        component'.Bindings.[0].Port1.Component =? (component' :> obj)
        component'.Bindings.[0].Port1.Method.Name =? "N"
        component'.Bindings.[0].Port2.IsRequiredPort =? false
        component'.Bindings.[0].Port2.Component =? (component' :> obj)
        component'.Bindings.[0].Port2.Method.Name =? "M"

    [<Test>]
    let ``returns instantaneous port binding of a component`` () =
        bindings "class X : Component { void M() {} extern void N(); public X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); } }"
        component'.Bindings.Length =? 1
        component'.Bindings.[0].Kind =? BindingKind.Instantaneous
        component'.Bindings.[0].Port1.IsRequiredPort =? true
        component'.Bindings.[0].Port1.Component =? (component' :> obj)
        component'.Bindings.[0].Port1.Method.Name =? "N"
        component'.Bindings.[0].Port2.IsRequiredPort =? false
        component'.Bindings.[0].Port2.Component =? (component' :> obj)
        component'.Bindings.[0].Port2.Method.Name =? "M"

    [<Test>]
    let ``returns multiple port binding between subcomponents`` () =
        bindings "class Y : Component { public void M() {} public extern void N(); } class X : Component { Y y1 = new Y(); Y y2 = new Y(); public X() { BindInstantaneous(y1.RequiredPorts.N = y2.ProvidedPorts.M); BindDelayed(y2.RequiredPorts.N = y1.ProvidedPorts.M); } }"
        component'.Bindings.Length =? 2
        component'.Bindings.[0].Kind =? BindingKind.Instantaneous
        component'.Bindings.[0].Port1.IsRequiredPort =? true
        component'.Bindings.[0].Port1.Component =? (component'.Subcomponents.[0] :> obj)
        component'.Bindings.[0].Port1.Method.Name =? "N"
        component'.Bindings.[0].Port2.IsRequiredPort =? false
        component'.Bindings.[0].Port2.Component =? (component'.Subcomponents.[1] :> obj)
        component'.Bindings.[0].Port2.Method.Name =? "M"
        component'.Bindings.[1].Kind =? BindingKind.Delayed
        component'.Bindings.[1].Port1.IsRequiredPort =? true
        component'.Bindings.[1].Port1.Component =? (component'.Subcomponents.[1] :> obj)
        component'.Bindings.[1].Port1.Method.Name =? "N"
        component'.Bindings.[1].Port2.IsRequiredPort =? false
        component'.Bindings.[1].Port2.Component =? (component'.Subcomponents.[0] :> obj)
        component'.Bindings.[1].Port2.Method.Name =? "M"

    [<Test>]
    let ``returns inherited port binding between subcomponents`` () =
        bindings "class Y : Component { public void M() {} public extern void N(); } class Z : Component { public Y y = new Y(); public Z() { BindDelayed(y.RequiredPorts.N = y.ProvidedPorts.M); } } class X : Z { public Y y2 = new Y(); public X() { BindDelayed(y.RequiredPorts.N = y2.ProvidedPorts.M); } }"
        component'.Bindings.Length =? 2
        component'.Bindings.[0].Kind =? BindingKind.Delayed
        component'.Bindings.[0].Port1.IsRequiredPort =? true
        component'.Bindings.[0].Port1.Component =? (component'.Subcomponents.[0] :> obj)
        component'.Bindings.[0].Port1.Method.Name =? "N"
        component'.Bindings.[0].Port2.IsRequiredPort =? false
        component'.Bindings.[0].Port2.Component =? (component'.Subcomponents.[0] :> obj)
        component'.Bindings.[0].Port2.Method.Name =? "M"
        component'.Bindings.[1].Kind =? BindingKind.Delayed
        component'.Bindings.[1].Port1.IsRequiredPort =? true
        component'.Bindings.[1].Port1.Component =? (component'.Subcomponents.[0] :> obj)
        component'.Bindings.[1].Port1.Method.Name =? "N"
        component'.Bindings.[1].Port2.IsRequiredPort =? false
        component'.Bindings.[1].Port2.Component =? (component'.Subcomponents.[1] :> obj)
        component'.Bindings.[1].Port2.Method.Name =? "M"

[<TestFixture>]
module ``Parent property`` =
    [<Test>]
    let ``throws when metadata has not yet been finalized`` () =
        let component' = OneSubcomponent (FieldComponent<int> 3)
        raisesInvalidOpException (fun () -> component'.Parent |> ignore)

    [<Test>]
    let ``returns null for root of hierarchy`` () =
        let component' = FieldComponent<int> 3
        component'.FinalizeMetadata ()
        component'.Parent =? null

    [<Test>]
    let ``returns root for subcomponent`` () =
        let component1 = FieldComponent<int> 3
        let component2 = OneSubcomponent component1
        component2.FinalizeMetadata ()
        component2.Parent =? null
        component1.Parent =? (component2 :> Component)

[<TestFixture>]
module ``Subcomponents property`` =
    [<Test>]
    let ``throws when metadata has not yet been finalized`` () =
        let component' = OneSubcomponent (FieldComponent<int> 3)
        raisesInvalidOpException (fun () -> component'.Subcomponents |> ignore)

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
        component'.FinalizeMetadata (null, "Root")

        component'.Subcomponents.[0].Name =? fsharpSubcomponentName "Root@0._component1" 0
        component'.Subcomponents.[1].Name =? fsharpSubcomponentName "Root@0._component2" 1

    [<Test>]
    let ``returns all subcomponents of the entire type hierarchy`` () =
        let csharpCode = "class S : Component {} class X : Component { S s = new S(); } class Y : X { S s1 = new S(); S s2 = new S(); }" 
        let compilation = TestCompilation csharpCode
        let assembly = compilation.Compile ()
        let derivedType = assembly.GetType "Y"
        let component' = Activator.CreateInstance derivedType :?> Component
        component'.FinalizeMetadata (null, "Root")

        component'.Subcomponents.Length =? 3
        component'.Subcomponents.[0].Name =? "Root@0.s@0"
        component'.Subcomponents.[1].Name =? "Root@0.s1@1"
        component'.Subcomponents.[2].Name =? "Root@0.s2@2"

    [<Test>]
    let ``all returned subcomponents have unique names`` () =
        let csharpCode = "class S : Component {} class X : Component { S s = new S(); } class Y : X { S s = new S(); }" 
        let compilation = TestCompilation csharpCode
        let assembly = compilation.Compile ()
        let derivedType = assembly.GetType "Y"
        let component' = Activator.CreateInstance derivedType :?> Component
        component'.FinalizeMetadata (null, "Root")

        component'.Subcomponents.Length =? 2
        component'.Subcomponents.[0].Name =? "Root@0.s@0"
        component'.Subcomponents.[1].Name =? "Root@0.s@1"

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
        raisesInvalidOpException (fun () -> component'.Access<bool> "xyz" |> ignore)

    [<Test>]
    let ``throws when field with given name exists but types differ`` () =
        let component' = FieldComponent<int> ()
        raisesInvalidOpException (fun () -> component'.Access<bool> (fsharpFieldName "_field") |> ignore)

        let component' = FieldComponent<int, bool> ()
        raisesInvalidOpException (fun () -> component'.Access<bool> (fsharpFieldName "_field1") |> ignore)
        raisesInvalidOpException (fun () -> component'.Access<int> (fsharpFieldName "_field2") |> ignore)

    [<Test>]
    let ``throws when property with given name exists but types differ`` () =
        let component' = FieldComponent<int> ()
        raisesInvalidOpException (fun () -> component'.Access<bool> "_field" |> ignore)

        let component' = FieldComponent<int, bool> ()
        raisesInvalidOpException (fun () -> component'.Access<bool> "_field1" |> ignore)
        raisesInvalidOpException (fun () -> component'.Access<int> "_field2" |> ignore)

    type SetterOnlyComponent () =
        inherit Component ()
        member this.X with set (value : int) = ()

    [<Test>]
    let ``throws when property has no getter`` () =
        let component' = SetterOnlyComponent ()
        raisesInvalidOpException (fun () -> component'.Access<int> "X" |> ignore)

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