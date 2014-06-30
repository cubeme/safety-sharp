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

namespace SafetySharp.Tests.CSharp.Transformation.SymbolTransformationTests

open System
open System.Linq
open NUnit.Framework
open Swensen.Unquote
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp
open SafetySharp.Metamodel
open SafetySharp.Modeling
open SafetySharp.Tests.CSharp
open SafetySharp.Tests
open SafetySharp.CSharp.Roslyn
open SafetySharp.CSharp.Transformation

[<AutoOpen>]
module private SymbolTransformationTestsHelper =
    let mutable symbolResolver = Unchecked.defaultof<SymbolResolver>
    let mutable compilation = Unchecked.defaultof<TestCompilation>
    let mutable components = Unchecked.defaultof<ComponentSymbol list>
    let mutable modelSymbol = Unchecked.defaultof<ModelSymbol>
    let mutable model = Unchecked.defaultof<Model>

    let compile csharpCode =
        compilation <- TestCompilation csharpCode
        symbolResolver <- SymbolTransformation.TransformComponentSymbols compilation.CSharpCompilation
        components <- symbolResolver.ComponentSymbols
        modelSymbol <- symbolResolver.ModelSymbol

    let compileModel csharpCode componentTypes = 
        compile csharpCode
        let components = componentTypes |> List.map compilation.CreateObject
        model <- TestModel (components |> Array.ofList)
        model.FinalizeMetadata ()
        symbolResolver <- SymbolTransformation.TransformModelSymbol symbolResolver model
        modelSymbol <- symbolResolver.ModelSymbol

[<TestFixture>]
module ``TransformComponentSymbols method`` =
    [<Test>]
    let ``throws when null compilation is passed`` () =
        raisesArgumentNullException "compilation" <@ SymbolTransformation.TransformComponentSymbols null @>

    [<Test>]
    let ``throws when null model is passed`` () =
        let compilation = TestCompilation("").CSharpCompilation
        raisesArgumentNullException "model" <@ SymbolTransformation.Transform compilation null @>

    [<Test>]
    let ``throws when non-finalized model is passed`` () =
        let compilation = TestCompilation("").CSharpCompilation
        let model = TestModel (EmptyComponent ())
        raisesArgumentException "model" <@ SymbolTransformation.Transform compilation model @>

[<TestFixture>]
module ``TransformModelSymbol method`` =
    [<Test>]
    let ``throws when null model is passed`` () =
        let compilation = TestCompilation("").CSharpCompilation
        let symbolResolver = SymbolTransformation.TransformComponentSymbols compilation
        raisesArgumentNullException "model" <@ SymbolTransformation.TransformModelSymbol symbolResolver null @>

    [<Test>]
    let ``throws when non-finalized model is passed`` () =
        let compilation = TestCompilation("").CSharpCompilation
        let symbolResolver = SymbolTransformation.TransformComponentSymbols compilation
        let model = TestModel (EmptyComponent ())
        raisesArgumentException "model" <@ SymbolTransformation.TransformModelSymbol symbolResolver model @>

[<TestFixture>]
module ``ModelSymbol property`` =
    [<Test>]
    let ``empty when compilation contains no components`` () =
        compile "class X {} class Y {}" 
        components =? []

    [<Test>]
    let ``contains all components`` () =
        compile "class A : Component {} class B : Component {} class C : Component {}"
        components =? [emptyComponentSymbol "A"; emptyComponentSymbol "B"; emptyComponentSymbol "C"]

    [<Test>]
    let ``does not contain non-component classes`` () =
        compile "class A {} class B {} class C : Component {}"
        components =? [emptyComponentSymbol "C"]

    [<Test>]
    let ``component name contains namespaces and nested types`` () =
        compile "namespace Test { class A : Component { } }"
        components.[0] =? emptyComponentSymbol "Test.A"

        compile "namespace Test1 { namespace Test2 { class A : Component { } }}"
        components.[0] =? emptyComponentSymbol "Test1.Test2.A"

        compile "namespace Test1.Test2 { class A : Component { } }"
        components.[0] =? emptyComponentSymbol "Test1.Test2.A"

        compile "namespace Test { class Nested { class A : Component { } }}"
        components.[0] =? emptyComponentSymbol "Test.Nested.A"

    [<Test>]
    let ``component symbol contains all fields`` () =
        compile "class A : Component { int i; bool b; decimal d; }"
        components.[0] =? { 
            emptyComponentSymbol "A" with 
                Fields = 
                [ 
                    { FieldSymbol.Name = "i"; Type = TypeSymbol.Integer }
                    { FieldSymbol.Name = "b"; Type = TypeSymbol.Boolean }
                    { FieldSymbol.Name = "d"; Type = TypeSymbol.Decimal }
                ] 
        }

    [<Test>]
    let ``all subcomponents are mapped`` () =
        compile "class A : Component { Component c; B b; IComponent i; } class B : Component {}"
        modelSymbol.Subcomponents.[modelSymbol.ComponentSymbols.[0]] =? 
        [ 
            { Name = "c"; ComponentSymbol = symbolResolver.ComponentBaseSymbol }
            { Name = "b"; ComponentSymbol = modelSymbol.ComponentSymbols.[1] }
            { Name = "i"; ComponentSymbol = symbolResolver.ComponentInterfaceSymbol }
        ] 

    [<Test>]
    let ``component symbol contains all provided ports`` () =
        compile "class A : Component { int M(int i, decimal d) { return 0; } void N(bool b) {} bool O() { return false; } }"
        components.[0].ProvidedPorts =? [ 
            ProvidedPort { 
                Name = "M"
                ReturnType = Some TypeSymbol.Integer 
                Parameters = [{ Name = "i"; Type = TypeSymbol.Integer }; { Name = "d"; Type = TypeSymbol.Decimal }]
                Locals = []
            }
            ProvidedPort { Name = "N"; ReturnType = None; Parameters = [{ Name = "b"; Type = TypeSymbol.Boolean }]; Locals = [] }
            ProvidedPort { Name = "O"; ReturnType = Some TypeSymbol.Boolean; Parameters = []; Locals = [] }
        ] 

    [<Test>]
    let ``component symbol contains all required ports`` () =
        compile "class A : Component { extern int M(int i, decimal d); extern void N(bool b); extern bool O(); }"
        components.[0].RequiredPorts =? [ 
            RequiredPort { 
                Name = "M"
                ReturnType = Some TypeSymbol.Integer 
                Parameters = [{ Name = "i"; Type = TypeSymbol.Integer }; { Name = "d"; Type = TypeSymbol.Decimal }]
                Locals = []
            }
            RequiredPort { Name = "N"; ReturnType = None; Parameters = [{ Name = "b"; Type = TypeSymbol.Boolean }]; Locals = [] }
            RequiredPort { Name = "O"; ReturnType = Some TypeSymbol.Boolean; Parameters = []; Locals = [] }
        ] 

    [<Test>]
    let ``component symbol contains update methods`` () =
        compile "class A : Component { public override void Update() { bool b; } }"
        components.[0].UpdateMethod =? { Name = "Update"; ReturnType = None; Parameters = []; Locals = [{ Name = "b"; Type = TypeSymbol.Boolean }] }

    [<Test>]
    let ``component symbol contains all data`` () =
        compile "class C : Component { extern bool M(int y); bool N(int x) { bool b = true; return b; } public override void Update() { int i; } int f; IComponent c; }"
        let componentSymbol = modelSymbol.ComponentSymbols.[0]
        componentSymbol =? {
            emptyComponentSymbol "C" with
                ProvidedPorts = [ProvidedPort {
                    Name = "N"
                    ReturnType = Some TypeSymbol.Boolean
                    Parameters = [{ Name = "x"; Type = TypeSymbol.Integer }]
                    Locals = [{ Name = "b"; Type = TypeSymbol.Boolean }]
                }]
                RequiredPorts = [RequiredPort {
                    Name = "M"
                    ReturnType = Some TypeSymbol.Boolean
                    Parameters = [{Name = "y"; Type = TypeSymbol.Integer}]
                    Locals = []
                }]
                Fields = [{ Name = "f"; Type = TypeSymbol.Integer }]
                UpdateMethod = { Name = "Update"; ReturnType = None; Parameters = []; Locals = [{ Name = "i"; Type = TypeSymbol.Integer }] }
        }

        modelSymbol.Subcomponents.[componentSymbol] =? [{ ComponentReferenceSymbol.Name = "c"; ComponentSymbol = symbolResolver.ComponentInterfaceSymbol }]

    [<Test>]
    let ``model contains partitions`` () =
        compileModel "class C : Component {}" ["C"]
        modelSymbol.Partitions =? [{ Name = "Root0"; RootComponent = components.[0] }]

        compileModel "class C : Component {} class D : Component { }" ["C"; "D"]
        modelSymbol.Partitions =? [{ Name = "Root0"; RootComponent = components.[0] }; { Name = "Root1"; RootComponent = components.[1] }]

    [<Test>]
    let ``model contains component objects`` () =
        compileModel "class C : Component {} class D : Component { C c = new C(); }" ["C"; "D"]
        modelSymbol.ComponentObjects =? 
        [
            { Name = "Root0"; ComponentSymbol = components.[0] }
            { Name = "Root1"; ComponentSymbol = components.[1] }
            { Name = "Root1.c"; ComponentSymbol = components.[0] }
        ]

[<TestFixture>]
module ``ResolveComponent(INamedTypeSymbol) method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        compile "class A : Component {} class B : Component {}"
        raisesArgumentNullException "componentSymbol" <@ symbolResolver.ResolveComponent (null : INamedTypeSymbol) @>

    [<Test>]
    let ``throws when non-component is passed`` () =
        compile "class A : Component {} class B {}"
        let classB = compilation.FindClassSymbol "B"

        raisesArgumentException "componentSymbol" <@ symbolResolver.ResolveComponent classB @>

    [<Test>]
    let ``returns symbol for transformed component`` () =
        compile "class A : Component {} class B : Component {}"
        let classA = compilation.FindClassSymbol "A"

        symbolResolver.ResolveComponent classA =? emptyComponentSymbol "A"

    [<Test>]
    let ``returns different symbols for different transformed components`` () =
        compile "class A : Component {} class B : Component {}"
        let classA = compilation.FindClassSymbol "A"
        let classB = compilation.FindClassSymbol "B"

        symbolResolver.ResolveComponent classA =? emptyComponentSymbol "A"
        symbolResolver.ResolveComponent classB =? emptyComponentSymbol "B"
        symbolResolver.ResolveComponent classA <>? symbolResolver.ResolveComponent classB

[<TestFixture>]
module ``ResolveComponent(Component) method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        compile "class A : Component {} class B : Component {}"
        raisesArgumentNullException "componentObject" <@ symbolResolver.ResolveComponent (null : Component) @>

    [<Test>]
    let ``throws when component object with unknown type is passed`` () =
        compile "class A : Component {}"
        raisesArgumentException "componentObject" <@ symbolResolver.ResolveComponent (EmptyComponent ()) @>

    [<Test>]
    let ``returns symbol for component object of transformed type`` () =
        compile "class A : Component {}"
        let componentA = compilation.CreateObject<Component> "A"

        symbolResolver.ResolveComponent componentA =? emptyComponentSymbol "A"

    [<Test>]
    let ``returns symbol for component object of deeply nested transformed type`` () =
        compile "namespace X.Y { struct Z { class A : Component {} }}"
        let componentA = compilation.CreateObject<Component> "X.Y.Z+A"

        symbolResolver.ResolveComponent componentA =? emptyComponentSymbol "X.Y.Z.A"

    [<Test>]
    let ``returns different symbols for different component objects with different transformed types`` () =
        compile "class A : Component {} class B : Component {}"
        let componentA = compilation.CreateObject<Component> "A"
        let componentB = compilation.CreateObject<Component> "B"

        symbolResolver.ResolveComponent componentA =? emptyComponentSymbol "A"
        symbolResolver.ResolveComponent componentB =? emptyComponentSymbol "B"
        symbolResolver.ResolveComponent componentA <>? symbolResolver.ResolveComponent componentB

    [<Test>]
    let ``returns same symbols for different component objects with same transformed types`` () =
        compile "class A : Component {}"
        let componentA = compilation.CreateObject<Component> "A"
        let componentB = compilation.CreateObject<Component> "A"

        componentA <>? componentB
        symbolResolver.ResolveComponent componentA =? emptyComponentSymbol "A"
        symbolResolver.ResolveComponent componentB =? emptyComponentSymbol "A"

        // We have to check for reference equality here
        test <@ obj.ReferenceEquals(symbolResolver.ResolveComponent componentA, symbolResolver.ResolveComponent componentB) @>

[<TestFixture>]
module ``ResolveField method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        compile "class A : Component {} class B : Component {}"
        raisesArgumentNullException "fieldSymbol" <@ symbolResolver.ResolveField null @>

    [<Test>]
    let ``throws when field of non-component is passed`` () =
        compile "class A : Component {} class B { int f; }"
        let field = compilation.FindFieldSymbol "B" "f"

        raisesArgumentException "fieldSymbol" <@ symbolResolver.ResolveField field @>

    [<Test>]
    let ``throws when subcomponent field is passed`` () =
        compile "class A : Component { B b; } class B : Component { }"
        let field = compilation.FindFieldSymbol "A" "b"

        raisesArgumentException "fieldSymbol" <@ symbolResolver.ResolveField field @>

    [<Test>]
    let ``returns symbol for field of transformed component`` () =
        compile "class A : Component { int f; } class B : Component {}"
        let field = compilation.FindFieldSymbol "A" "f"

        symbolResolver.ResolveField field =? { Name = "f"; Type = TypeSymbol.Integer }

    [<Test>]
    let ``returns different symbols for different fields of same transformed component`` () =
        compile "class A : Component { int f; bool g; } class B : Component {}"
        let field1 = compilation.FindFieldSymbol "A" "f"
        let field2 = compilation.FindFieldSymbol "A" "g"

        symbolResolver.ResolveField field1 =? { Name = "f"; Type = TypeSymbol.Integer }
        symbolResolver.ResolveField field2 =? { Name = "g"; Type = TypeSymbol.Boolean }
        symbolResolver.ResolveField field1 <>? symbolResolver.ResolveField field2

    [<Test>]
    let ``returns different symbols for different fields of different transformed components`` () =
        compile "class A : Component { int f; } class B : Component { int f; int g; }"
        let field1 = compilation.FindFieldSymbol "A" "f"
        let field2 = compilation.FindFieldSymbol "B" "f"
        let field3 = compilation.FindFieldSymbol "B" "g"

        symbolResolver.ResolveField field1 =? { Name = "f"; Type = TypeSymbol.Integer }
        symbolResolver.ResolveField field2 =? { Name = "f"; Type = TypeSymbol.Integer }
        symbolResolver.ResolveField field3 =? { Name = "g"; Type = TypeSymbol.Integer }

        // We have to check for reference equality here
        test <@ not <| obj.ReferenceEquals(symbolResolver.ResolveField field1, symbolResolver.ResolveField field2) @>

[<TestFixture>]
module ``ResolveSubcomponent method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        compile "class A : Component {} class B : Component {}"
        raisesArgumentNullException "subcomponentSymbol" <@ symbolResolver.ResolveSubcomponent null @>

    [<Test>]
    let ``throws when subcomponent of non-component is passed`` () =
        compile "class A : Component {} class B { A f; }"
        let field = compilation.FindFieldSymbol "B" "f"

        raisesArgumentException "subcomponentSymbol" <@ symbolResolver.ResolveSubcomponent field @>

    [<Test>]
    let ``throws when non-subcomponent field is passed`` () =
        compile "class A : Component { int b; } class B : Component { }"
        let field = compilation.FindFieldSymbol "A" "b"

        raisesArgumentException "subcomponentSymbol" <@ symbolResolver.ResolveSubcomponent field @>

    [<Test>]
    let ``returns symbol for IComponent for subcomponent of type IComponent`` () =
        compile "class A : Component { IComponent c; }"
        let field = compilation.FindFieldSymbol "A" "c"

        modelSymbol.Subcomponents.[components.[0]].[0].ComponentSymbol =? symbolResolver.ComponentInterfaceSymbol

    [<Test>]
    let ``returns symbol for Component for subcomponent of type Component`` () =
        compile "class A : Component { Component c; }"
        let field = compilation.FindFieldSymbol "A" "c"

        modelSymbol.Subcomponents.[components.[0]].[0].ComponentSymbol =? symbolResolver.ComponentBaseSymbol

    [<Test>]
    let ``returns symbol for subcomponent of transformed component`` () =
        compile "class A : Component { B f; } class B : Component {}"
        let field = compilation.FindFieldSymbol "A" "f"

        symbolResolver.ResolveSubcomponent field =? { Name = "f"; ComponentSymbol = components.[1] }

    [<Test>]
    let ``returns different symbols for different subcomponents of same transformed component`` () =
        compile "class A : Component { B b1; B b2; } class B : Component {}"
        let field1 = compilation.FindFieldSymbol "A" "b1"
        let field2 = compilation.FindFieldSymbol "A" "b2"

        symbolResolver.ResolveSubcomponent field1 =? { Name = "b1"; ComponentSymbol = components.[1] }
        symbolResolver.ResolveSubcomponent field2 =? { Name = "b2"; ComponentSymbol = components.[1] }
        symbolResolver.ResolveSubcomponent field1 <>? symbolResolver.ResolveSubcomponent field2

    [<Test>]
    let ``returns different symbols for different subcomponents of different transformed components`` () =
        compile "class A : Component { B b; } class B : Component { A a1; A a2; }"
        let field1 = compilation.FindFieldSymbol "A" "b"
        let field2 = compilation.FindFieldSymbol "B" "a1"
        let field3 = compilation.FindFieldSymbol "B" "a2"

        symbolResolver.ResolveSubcomponent field1 =? { Name = "b"; ComponentSymbol = components.[1]}
        symbolResolver.ResolveSubcomponent field2 =? { Name = "a1"; ComponentSymbol = components.[0] }
        symbolResolver.ResolveSubcomponent field3 =? { Name = "a2"; ComponentSymbol = components.[0] }

        // We have to check for reference equality here
        test <@ not <| obj.ReferenceEquals(symbolResolver.ResolveSubcomponent field1, symbolResolver.ResolveSubcomponent field2) @>
        
[<TestFixture>]
module ``ResolveParameter method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        compile "class A : Component { void M(int i) {} }"
        raisesArgumentNullException "parameterSymbol" <@ symbolResolver.ResolveParameter null @>

    [<Test>]
    let ``throws when a parameter of non-component method is passed`` () =
        compile "class A { void M(int i) {} }"
        let parameterSymbol = compilation.FindParameterSymbol "A" "M" "i"
        raisesArgumentException "parameterSymbol" <@ symbolResolver.ResolveParameter parameterSymbol @>

    [<Test>]
    let ``returns symbol for parameter of transformed component method`` () =
        compile "class A : Component { void M(int i) {} }"
        let parameter = compilation.FindParameterSymbol "A" "M" "i"
        symbolResolver.ResolveParameter parameter =? { Name = "i"; Type = TypeSymbol.Integer }

    [<Test>]
    let ``returns different symbols for different parameters of same transformed component method`` () =
        compile "class A : Component { void M(int i, bool b) {} }"
        let parameter1 = compilation.FindParameterSymbol "A" "M" "i"
        let parameter2 = compilation.FindParameterSymbol "A" "M" "b"

        symbolResolver.ResolveParameter parameter1 =? { Name = "i"; Type = TypeSymbol.Integer }
        symbolResolver.ResolveParameter parameter2 =? { Name = "b"; Type = TypeSymbol.Boolean }
        symbolResolver.ResolveParameter parameter1 <>? symbolResolver.ResolveParameter parameter2

    [<Test>]
    let ``returns different symbols for different parameters of different transformed component methods`` () =
        compile "class A : Component { void M(int i, bool b) {} } class B : Component { void M(int i) {} }"
        let parameter1 = compilation.FindParameterSymbol "A" "M" "i"
        let parameter2 = compilation.FindParameterSymbol "A" "M" "b"
        let parameter3 = compilation.FindParameterSymbol "B" "M" "i"

        symbolResolver.ResolveParameter parameter1 =? { Name = "i"; Type = TypeSymbol.Integer }
        symbolResolver.ResolveParameter parameter2 =? { Name = "b"; Type = TypeSymbol.Boolean }
        symbolResolver.ResolveParameter parameter3 =? { Name = "i"; Type = TypeSymbol.Integer }

        // We have to check for reference equality here
        test <@ not <| obj.ReferenceEquals(symbolResolver.ResolveParameter parameter1, symbolResolver.ResolveParameter parameter3) @>

[<TestFixture>]
module ``ResolveLocal method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        compile "class A : Component { void M(int i) {} }"
        raisesArgumentNullException "localSymbol" <@ symbolResolver.ResolveLocal null @>

    [<Test>]
    let ``throws when a local of non-component method is passed`` () =
        compile "class A { void M() { int a; } }"
        let localSymbol = compilation.FindLocalSymbol "A" "M" "a"
        raisesArgumentException "localSymbol" <@ symbolResolver.ResolveLocal localSymbol @>

    [<Test>]
    let ``returns symbol for local of transformed component method`` () =
        compile "class A : Component { void M() { int i; } }"
        let localSymbol = compilation.FindLocalSymbol "A" "M" "i"
        symbolResolver.ResolveLocal localSymbol =? { Name = "i"; Type = TypeSymbol.Integer }

    [<Test>]
    let ``returns different symbols for different locals of same transformed component method`` () =
        compile "class A : Component { void M() { int i, j; bool b; if (true) { decimal d; } } }"
        let local1 = compilation.FindLocalSymbol "A" "M" "i"
        let local2 = compilation.FindLocalSymbol "A" "M" "j"
        let local3 = compilation.FindLocalSymbol "A" "M" "b"
        let local4 = compilation.FindLocalSymbol "A" "M" "d"

        symbolResolver.ResolveLocal local1 =? { Name = "i"; Type = TypeSymbol.Integer }
        symbolResolver.ResolveLocal local2 =? { Name = "j"; Type = TypeSymbol.Integer }
        symbolResolver.ResolveLocal local3 =? { Name = "b"; Type = TypeSymbol.Boolean }
        symbolResolver.ResolveLocal local4 =? { Name = "d"; Type = TypeSymbol.Decimal }

    [<Test>]
    let ``returns different symbols for different locals of different transformed component methods`` () =
        compile "class A : Component { void M() { int a; } } class B : Component { void M() { int a; } }"
        let local1 = compilation.FindLocalSymbol "A" "M" "a"
        let local2 = compilation.FindLocalSymbol "B" "M" "a"

        symbolResolver.ResolveLocal local1 =? { Name = "a"; Type = TypeSymbol.Integer }
        symbolResolver.ResolveLocal local2 =? { Name = "a"; Type = TypeSymbol.Integer }

        // We have to check for reference equality here
        test <@ not <| obj.ReferenceEquals(symbolResolver.ResolveLocal local1, symbolResolver.ResolveLocal local2) @>

[<TestFixture>]
module ``ResolveMethod method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        compile "class A : Component {} class B : Component {}"
        raisesArgumentNullException "methodSymbol" <@ symbolResolver.ResolveMethod null @>

    [<Test>]
    let ``throws when method of non-component is passed`` () =
        compile "class A : Component {} class B { void M() {} }"
        let methodSymbol = compilation.FindMethodSymbol "B" "M"

        raisesArgumentException "methodSymbol" <@ symbolResolver.ResolveMethod methodSymbol @>

    [<Test>]
    let ``throws when constructor is passed`` () =
        compile "class A : Component { int b; } class B : Component { }"
        let classSymbol = compilation.FindClassSymbol "A"
        let constructorSymbol = classSymbol.GetMembers().OfType<IMethodSymbol>().Single(fun method' -> method'.MethodKind = MethodKind.Constructor)

        raisesArgumentException "methodSymbol" <@ symbolResolver.ResolveMethod constructorSymbol @>

    [<Test>]
    let ``returns symbol for method of transformed component`` () =
        compile "class A : Component { void M() {} } class B : Component {}"
        let methodSymbol = compilation.FindMethodSymbol "A" "M"

        symbolResolver.ResolveMethod methodSymbol =? { Name = "M"; ReturnType = None; Parameters = []; Locals = [] }

    [<Test>]
    let ``returns update method symbol for update method of transformed component`` () =
        compile "class A : Component { public override void Update() {} } class B : Component {}"
        let classSymbol = compilation.FindClassSymbol "A"
        let methodSymbol = compilation.FindMethodSymbol "A" "Update"
        let componentSymbol = symbolResolver.ResolveComponent classSymbol

        symbolResolver.ResolveMethod methodSymbol =? { Name = "Update"; ReturnType = None; Parameters = []; Locals = [] }

        // We have to check for reference equality here
        test <@ obj.ReferenceEquals(componentSymbol.UpdateMethod, symbolResolver.ResolveMethod methodSymbol) @>

    [<Test>]
    let ``returns base update method symbol for transformed component that does not override update method`` () =
        compile "class A : Component {}"
        let classSymbol = compilation.FindClassSymbol "A"
        let methodSymbol = compilation.FindMethodSymbol "SafetySharp.Modeling.Component" "Update"
        let componentSymbol = symbolResolver.ResolveComponent classSymbol

        symbolResolver.ResolveMethod methodSymbol =? { Name = "Update"; ReturnType = None; Parameters = []; Locals = [] }

        // We have to check for reference equality here
        test <@ obj.ReferenceEquals(componentSymbol.UpdateMethod, symbolResolver.ResolveMethod methodSymbol) @>

    [<Test>]
    let ``returns overriden base update method symbol for transformed component that does not override update method`` () =
        compile "class A : B {} class B : Component { public override void Update () {} }"
        let classSymbol = compilation.FindClassSymbol "A"
        let methodSymbol = compilation.FindMethodSymbol "B" "Update"
        let componentSymbol = symbolResolver.ResolveComponent classSymbol

        symbolResolver.ResolveMethod methodSymbol =? { Name = "Update"; ReturnType = None; Parameters = []; Locals = [] }

        // We have to check for reference equality here
        test <@ obj.ReferenceEquals(componentSymbol.UpdateMethod, symbolResolver.ResolveMethod methodSymbol) @>

    [<Test>]
    let ``returns different symbols for different methods of same transformed component`` () =
        compile "class A : Component { void M() {} void N() {} } class B : Component {}"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "A" "N"

        symbolResolver.ResolveMethod method1 =? { Name = "M"; ReturnType = None; Parameters = []; Locals = [] }
        symbolResolver.ResolveMethod method2 =? { Name = "N"; ReturnType = None; Parameters = []; Locals = [] }
        symbolResolver.ResolveMethod method1 <>? symbolResolver.ResolveMethod method2

    [<Test>]
    let ``returns different symbols for different methods of different transformed components`` () =
        compile "class A : Component { void M() {} } class B : Component { void M() {} void N() {} }"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "B" "M"
        let method3 = compilation.FindMethodSymbol "B" "N"

        symbolResolver.ResolveMethod method1 =? { Name = "M"; ReturnType = None; Parameters = []; Locals = [] }
        symbolResolver.ResolveMethod method2 =? { Name = "M"; ReturnType = None; Parameters = []; Locals = [] }
        symbolResolver.ResolveMethod method3 =? { Name = "N"; ReturnType = None; Parameters = []; Locals = [] }

        // We have to check for reference equality here
        test <@ not <| obj.ReferenceEquals(symbolResolver.ResolveMethod method1, symbolResolver.ResolveMethod method2) @>

[<TestFixture>]
module ``ResolveCSharpMethod method`` =
    [<Test>]
    let ``throws when method of non-component is passed`` () =
        compile "class A : Component {} class B { void M() {} }"
        let methodSymbol = compilation.FindMethodSymbol "B" "M"

        raisesArgumentException "methodSymbol" <@ symbolResolver.ResolveCSharpMethod <| symbolResolver.ResolveMethod methodSymbol @> 

    [<Test>]
    let ``returns symbol for method of transformed component`` () =
        compile "class A : Component { void M() {} } class B : Component {}"
        let methodSymbol = compilation.FindMethodSymbol "A" "M"

        symbolResolver.ResolveMethod methodSymbol |> symbolResolver.ResolveCSharpMethod =? methodSymbol

    [<Test>]
    let ``returns update method symbol for update method of transformed component`` () =
        compile "class A : Component { public override void Update() {} }"
        let classSymbol = compilation.FindClassSymbol "A"
        let methodSymbol = compilation.FindMethodSymbol "A" "Update"
        let componentSymbol = symbolResolver.ResolveComponent classSymbol

        symbolResolver.ResolveMethod methodSymbol |> symbolResolver.ResolveCSharpMethod =? methodSymbol
        symbolResolver.ResolveCSharpMethod componentSymbol.UpdateMethod =? methodSymbol

    [<Test>]
    let ``returns base update method symbol for transformed component that does not override update method`` () =
        compile "class A : Component {}"
        let classSymbol = compilation.FindClassSymbol "A"
        let methodSymbol = compilation.FindMethodSymbol "SafetySharp.Modeling.Component" "Update"
        let componentSymbol = symbolResolver.ResolveComponent classSymbol

        symbolResolver.ResolveMethod methodSymbol |> symbolResolver.ResolveCSharpMethod =? methodSymbol
        symbolResolver.ResolveCSharpMethod componentSymbol.UpdateMethod =? methodSymbol

    [<Test>]
    let ``returns overriden base update method symbol for transformed component that does not override update method`` () =
        compile "class A : B {} class B : Component { public override void Update () {} }"
        let classSymbol = compilation.FindClassSymbol "A"
        let methodSymbol = compilation.FindMethodSymbol "B" "Update"
        let componentSymbol = symbolResolver.ResolveComponent classSymbol

        symbolResolver.ResolveMethod methodSymbol |> symbolResolver.ResolveCSharpMethod =? methodSymbol
        symbolResolver.ResolveCSharpMethod componentSymbol.UpdateMethod =? methodSymbol

    [<Test>]
    let ``returns different symbols for different methods of same transformed component`` () =
        compile "class A : Component { void M() {} void N() {} } class B : Component {}"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "A" "N"

        symbolResolver.ResolveMethod method1 |> symbolResolver.ResolveCSharpMethod =? method1
        symbolResolver.ResolveMethod method2 |> symbolResolver.ResolveCSharpMethod =? method2

    [<Test>]
    let ``returns different symbols for different methods of different transformed components`` () =
        compile "class A : Component { void M() {} } class B : Component { void M() {} void N() {} }"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "B" "M"
        let method3 = compilation.FindMethodSymbol "B" "N"

        symbolResolver.ResolveMethod method1 |> symbolResolver.ResolveCSharpMethod =? method1
        symbolResolver.ResolveMethod method2 |> symbolResolver.ResolveCSharpMethod =? method2
        symbolResolver.ResolveMethod method3 |> symbolResolver.ResolveCSharpMethod =? method3

[<TestFixture>]
module ``ResolveComponentReference method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        compileModel "class A : Component {}" ["A"]
        raisesArgumentNullException "componentObject" <@ symbolResolver.ResolveComponentReference (null : Component) @>

    [<Test>]
    let ``throws when component object with unknown type is passed`` () =
        compileModel "class A : Component {}" ["A"]
        let component' = EmptyComponent ()
        component'.FinalizeMetadata ()
        raisesArgumentException "componentObject" <@ symbolResolver.ResolveComponentReference component' @>

    [<Test>]
    let ``throws when component objects have not yet been transformed`` () =
        compile "class A : Component {}"
        let component' = EmptyComponent ()
        component'.FinalizeMetadata ()
        raises<InvalidOperationException> <@ symbolResolver.ResolveComponentReference component' @>

    [<Test>]
    let ``returns symbol for partition root component reference`` () =
        compileModel "class A : Component {}" ["A"]
        let componentA = model.PartitionRoots.[0]
        symbolResolver.ResolveComponentReference componentA =? { Name = "Root0"; ComponentSymbol = components.[0] }

    [<Test>]
    let ``returns symbol for nested component reference`` () =
        compileModel "class A : Component {} class B : A { A a = new A(); }" ["B"]
        let componentA = model.PartitionRoots.[0].GetSubcomponent "a"
        symbolResolver.ResolveComponentReference componentA =? { Name = "Root0.a"; ComponentSymbol = components.[0] }

    [<Test>]
    let ``returns different symbols for different components`` () =
        compileModel "class A : Component {} class B : A { A a = new A(); }" ["B"; "B"]
        let componentA1 = model.PartitionRoots.[0].GetSubcomponent "a"
        let componentA2 = model.PartitionRoots.[1].GetSubcomponent "a"
        symbolResolver.ResolveComponentReference componentA1 =? { Name = "Root0.a"; ComponentSymbol = components.[0] }
        symbolResolver.ResolveComponentReference componentA2 =? { Name = "Root1.a"; ComponentSymbol = components.[0] }

        symbolResolver.ResolveComponentReference componentA1 <>? symbolResolver.ResolveComponentReference componentA2

[<TestFixture>]
module ``ResolvePartition method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        compileModel "class A : Component {}" ["A"]
        raisesArgumentNullException "componentObject" <@ symbolResolver.ResolvePartition (null : Component) @>

    [<Test>]
    let ``throws when component object with unknown type is passed`` () =
        compileModel "class A : Component {}" ["A"]
        let component' = EmptyComponent ()
        component'.FinalizeMetadata ()
        raisesArgumentException "componentObject" <@ symbolResolver.ResolvePartition component' @>

    [<Test>]
    let ``throws when component objects have not yet been transformed`` () =
        compile "class A : Component {}"
        let component' = EmptyComponent ()
        component'.FinalizeMetadata ()
        raises<InvalidOperationException> <@ symbolResolver.ResolvePartition component' @>

    [<Test>]
    let ``returns symbol for single partition`` () =
        compileModel "class A : Component {}" ["A"]
        symbolResolver.ResolvePartition  model.PartitionRoots.[0] =? { Name = "Root0"; RootComponent = components.[0] }

    [<Test>]
    let ``returns symbols for multiple partitions of some type`` () =
        compileModel "class A : Component {}" ["A"; "A"; "A"]
        symbolResolver.ResolvePartition  model.PartitionRoots.[0] =? { Name = "Root0"; RootComponent = components.[0] }
        symbolResolver.ResolvePartition  model.PartitionRoots.[1] =? { Name = "Root1"; RootComponent = components.[0] }
        symbolResolver.ResolvePartition  model.PartitionRoots.[2] =? { Name = "Root2"; RootComponent = components.[0] }

    [<Test>]
    let ``returns symbols for multiple partitions of different types`` () =
        compileModel "class A : Component {} class B : Component {}" ["A"; "B"; "A"]
        symbolResolver.ResolvePartition  model.PartitionRoots.[0] =? { Name = "Root0"; RootComponent = components.[0] }
        symbolResolver.ResolvePartition  model.PartitionRoots.[1] =? { Name = "Root1"; RootComponent = components.[1] }
        symbolResolver.ResolvePartition  model.PartitionRoots.[2] =? { Name = "Root2"; RootComponent = components.[0] }