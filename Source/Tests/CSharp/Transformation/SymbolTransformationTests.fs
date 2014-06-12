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

namespace SafetySharp.Tests.CSharp.SymbolTransformationTests

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

[<AutoOpen>]
module private SymbolTransformationTestsHelper =
    let compile csharpCode =
        let compilation = TestCompilation csharpCode
        SymbolTransformation.Transform compilation.CSharpCompilation

    let components csharpCode =
        let resolver = compile csharpCode
        resolver.ComponentSymbols

    let emptyUpdate = { Name = "Update"; ReturnType = None; Parameters = [] }
    let emptyComponent name = { Name = "TestCompilation::" + name; UpdateMethod = emptyUpdate; Fields = []; Methods = []; Subcomponents = [] } 

[<TestFixture>]
module ``Transform method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        raisesArgumentNullException "compilation" <@ SymbolTransformation.Transform null @>

[<TestFixture>]
module ``ComponentSymbols property`` =
    [<Test>]
    let ``empty when compilation contains no components`` () =
        components "class X {} class Y {}" =? []

    [<Test>]
    let ``contains all components`` () =
        components "class A : Component {} class B : Component {} class C : Component {}"
        =? [emptyComponent "A"; emptyComponent "B"; emptyComponent "C"]

    [<Test>]
    let ``does not contain non-component classes`` () =
        components "class A {} class B {} class C : Component {}"
        =? [emptyComponent "C"]

    [<Test>]
    let ``component name contains namespaces and nested types`` () =
        let transformedComponents = components "namespace Test { class A : Component { } }"
        transformedComponents.[0] =? emptyComponent "Test.A"

        let transformedComponents = components "namespace Test1 { namespace Test2 { class A : Component { } }}"
        transformedComponents.[0] =? emptyComponent "Test1.Test2.A"

        let transformedComponents = components "namespace Test1.Test2 { class A : Component { } }"
        transformedComponents.[0] =? emptyComponent "Test1.Test2.A"

        let transformedComponents = components "namespace Test { class Nested { class A : Component { } }}"
        transformedComponents.[0] =? emptyComponent "Test.Nested.A"

    [<Test>]
    let ``component symbol contains all fields`` () =
        let components = components "class A : Component { int i; bool b; decimal d; }"
        components.[0] =? { 
            emptyComponent "A" with 
                Fields = 
                [ 
                    { FieldSymbol.Name = "i"; Type = TypeSymbol.Integer }
                    { FieldSymbol.Name = "b"; Type = TypeSymbol.Boolean }
                    { FieldSymbol.Name = "d"; Type = TypeSymbol.Decimal }
                ] 
        }

    [<Test>]
    let ``component symbol contains all subcomponents`` () =
        let components = components "class A : Component { Component c; B b; IComponent i; } class B : Component {}"
        components.[0] =? { 
            emptyComponent "A" with 
                Subcomponents = 
                [ 
                    { SubcomponentSymbol.Name = "c" }
                    { SubcomponentSymbol.Name = "b" }
                    { SubcomponentSymbol.Name = "i" }
                ] 
        }

    [<Test>]
    let ``component symbol contains all non-update methods`` () =
        let components = components "class A : Component { int M(int i, decimal d) { return 0; } void N(bool b) {} bool O() { return false; } }"
        components.[0] =? { 
            emptyComponent "A" with 
                Methods = 
                [ 
                    { 
                        MethodSymbol.Name = "M"
                        ReturnType = Some TypeSymbol.Integer 
                        Parameters = [{ ParameterSymbol.Name = "i"; Type = TypeSymbol.Integer }; { ParameterSymbol.Name = "d"; Type = TypeSymbol.Decimal }]
                    }
                    { MethodSymbol.Name = "N"; ReturnType = None; Parameters = [{ ParameterSymbol.Name = "b"; Type = TypeSymbol.Boolean }] }
                    { MethodSymbol.Name = "O"; ReturnType = Some TypeSymbol.Boolean; Parameters = [] }
                ] 
        }

    [<Test>]
    let ``component symbol contains update methods`` () =
        let components = components "class A : Component { public override void Update() {} }"
        components.[0] =? { emptyComponent "A" with UpdateMethod = { MethodSymbol.Name = "Update"; ReturnType = None; Parameters = [] } }

    [<Test>]
    let ``component symbol contains all data`` () =
        let components = components "class C : Component { bool N(int x) { return false; } public override void Update() {} int f; IComponent c; }"
        components.[0] =? {
            emptyComponent "C" with
                Methods = [{ MethodSymbol.Name = "N"; ReturnType = Some TypeSymbol.Boolean; Parameters = [{ ParameterSymbol.Name = "x"; Type = TypeSymbol.Integer }] }]
                Fields = [{ FieldSymbol.Name = "f"; Type = TypeSymbol.Integer }]
                Subcomponents = [{ SubcomponentSymbol.Name = "c" }]
                UpdateMethod = { MethodSymbol.Name = "Update"; ReturnType = None; Parameters = [] }
        }

[<TestFixture>]
module ``ResolveComponent(INamedTypeSymbol) method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        let resolver = compile "class A : Component {} class B : Component {}"
        raisesArgumentNullException "componentSymbol" <@ resolver.ResolveComponent (null : INamedTypeSymbol) @>

    [<Test>]
    let ``throws when non-component is passed`` () =
        let compilation = TestCompilation "class A : Component {} class B {}"
        let classB = compilation.FindClassSymbol "B"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        raisesArgumentException "componentSymbol" <@ resolver.ResolveComponent classB @>

    [<Test>]
    let ``returns symbol for transformed component`` () =
        let compilation = TestCompilation "class A : Component {} class B : Component {}"
        let classA = compilation.FindClassSymbol "A"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveComponent classA =? emptyComponent "A"

    [<Test>]
    let ``returns different symbols for different transformed components`` () =
        let compilation = TestCompilation "class A : Component {} class B : Component {}"
        let classA = compilation.FindClassSymbol "A"
        let classB = compilation.FindClassSymbol "B"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveComponent classA =? emptyComponent "A"
        resolver.ResolveComponent classB =? emptyComponent "B"
        resolver.ResolveComponent classA <>? resolver.ResolveComponent classB

[<TestFixture>]
module ``ResolveComponent(Component) method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        let resolver = compile "class A : Component {} class B : Component {}"
        raisesArgumentNullException "componentObject" <@ resolver.ResolveComponent (null : Component) @>

    [<Test>]
    let ``throws when component object with unknown type is passed`` () =
        let compilation = TestCompilation "class A : Component {}"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        raisesArgumentException "componentObject" <@ resolver.ResolveComponent (EmptyComponent ()) @>

    [<Test>]
    let ``returns symbol for component object of transformed type`` () =
        let compilation = TestCompilation "class A : Component {}"
        let componentA = compilation.CreateObject<Component> "A"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveComponent componentA =? emptyComponent "A"

    [<Test>]
    let ``returns symbol for component object of deeply nested transformed type`` () =
        let compilation = TestCompilation "namespace X.Y { struct Z { class A : Component {} }}"
        let componentA = compilation.CreateObject<Component> "X.Y.Z+A"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveComponent componentA =? emptyComponent "X.Y.Z.A"

    [<Test>]
    let ``returns different symbols for different component objects with different transformed types`` () =
        let compilation = TestCompilation "class A : Component {} class B : Component {}"
        let componentA = compilation.CreateObject<Component> "A"
        let componentB = compilation.CreateObject<Component> "B"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveComponent componentA =? emptyComponent "A"
        resolver.ResolveComponent componentB =? emptyComponent "B"
        resolver.ResolveComponent componentA <>? resolver.ResolveComponent componentB

    [<Test>]
    let ``returns same symbols for different component objects with same transformed types`` () =
        let compilation = TestCompilation "class A : Component {}"
        let componentA = compilation.CreateObject<Component> "A"
        let componentB = compilation.CreateObject<Component> "A"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        componentA <>? componentB
        resolver.ResolveComponent componentA =? emptyComponent "A"
        resolver.ResolveComponent componentB =? emptyComponent "A"

        // We have to check for reference equality here
        test <@ obj.ReferenceEquals(resolver.ResolveComponent componentA, resolver.ResolveComponent componentB) @>

[<TestFixture>]
module ``ResolveField method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        let resolver = compile "class A : Component {} class B : Component {}"
        raisesArgumentNullException "fieldSymbol" <@ resolver.ResolveField null @>

    [<Test>]
    let ``throws when field of non-component is passed`` () =
        let compilation = TestCompilation "class A : Component {} class B { int f; }"
        let field = compilation.FindFieldSymbol "B" "f"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        raisesArgumentException "fieldSymbol" <@ resolver.ResolveField field @>

    [<Test>]
    let ``throws when subcomponent field is passed`` () =
        let compilation = TestCompilation "class A : Component { B b; } class B : Component { }"
        let field = compilation.FindFieldSymbol "A" "b"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        raisesArgumentException "fieldSymbol" <@ resolver.ResolveField field @>

    [<Test>]
    let ``returns symbol for field of transformed component`` () =
        let compilation = TestCompilation "class A : Component { int f; } class B : Component {}"
        let field = compilation.FindFieldSymbol "A" "f"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveField field =? { FieldSymbol.Name = "f"; Type = TypeSymbol.Integer }

    [<Test>]
    let ``returns different symbols for different fields of same transformed component`` () =
        let compilation = TestCompilation "class A : Component { int f; bool g; } class B : Component {}"
        let field1 = compilation.FindFieldSymbol "A" "f"
        let field2 = compilation.FindFieldSymbol "A" "g"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveField field1 =? { FieldSymbol.Name = "f"; Type = TypeSymbol.Integer }
        resolver.ResolveField field2 =? { FieldSymbol.Name = "g"; Type = TypeSymbol.Boolean }
        resolver.ResolveField field1 <>? resolver.ResolveField field2

    [<Test>]
    let ``returns different symbols for different fields of different transformed components`` () =
        let compilation = TestCompilation "class A : Component { int f; } class B : Component { int f; int g; }"
        let field1 = compilation.FindFieldSymbol "A" "f"
        let field2 = compilation.FindFieldSymbol "B" "f"
        let field3 = compilation.FindFieldSymbol "B" "g"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveField field1 =? { FieldSymbol.Name = "f"; Type = TypeSymbol.Integer }
        resolver.ResolveField field2 =? { FieldSymbol.Name = "f"; Type = TypeSymbol.Integer }
        resolver.ResolveField field3 =? { FieldSymbol.Name = "g"; Type = TypeSymbol.Integer }

        // We have to check for reference equality here
        test <@ not <| obj.ReferenceEquals(resolver.ResolveField field1, resolver.ResolveField field2) @>

[<TestFixture>]
module ``ResolveSubcomponent method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        let resolver = compile "class A : Component {} class B : Component {}"
        raisesArgumentNullException "subcomponentSymbol" <@ resolver.ResolveSubcomponent null @>

    [<Test>]
    let ``throws when subcomponent of non-component is passed`` () =
        let compilation = TestCompilation "class A : Component {} class B { A f; }"
        let field = compilation.FindFieldSymbol "B" "f"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        raisesArgumentException "subcomponentSymbol" <@ resolver.ResolveSubcomponent field @>

    [<Test>]
    let ``throws when non-subcomponent field is passed`` () =
        let compilation = TestCompilation "class A : Component { int b; } class B : Component { }"
        let field = compilation.FindFieldSymbol "A" "b"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        raisesArgumentException "subcomponentSymbol" <@ resolver.ResolveSubcomponent field @>

    [<Test>]
    let ``returns symbol for subcomponent of transformed component`` () =
        let compilation = TestCompilation "class A : Component { B f; } class B : Component {}"
        let field = compilation.FindFieldSymbol "A" "f"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveSubcomponent field =? { SubcomponentSymbol.Name = "f" }

    [<Test>]
    let ``returns different symbols for different subcomponents of same transformed component`` () =
        let compilation = TestCompilation "class A : Component { B b1; B b2; } class B : Component {}"
        let field1 = compilation.FindFieldSymbol "A" "b1"
        let field2 = compilation.FindFieldSymbol "A" "b2"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveSubcomponent field1 =? { SubcomponentSymbol.Name = "b1" }
        resolver.ResolveSubcomponent field2 =? { SubcomponentSymbol.Name = "b2" }
        resolver.ResolveSubcomponent field1 <>? resolver.ResolveSubcomponent field2

    [<Test>]
    let ``returns different symbols for different subcomponents of different transformed components`` () =
        let compilation = TestCompilation "class A : Component { B b; } class B : Component { A a1; A a2; }"
        let field1 = compilation.FindFieldSymbol "A" "b"
        let field2 = compilation.FindFieldSymbol "B" "a1"
        let field3 = compilation.FindFieldSymbol "B" "a2"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveSubcomponent field1 =? { SubcomponentSymbol.Name = "b" }
        resolver.ResolveSubcomponent field2 =? { SubcomponentSymbol.Name = "a1" }
        resolver.ResolveSubcomponent field3 =? { SubcomponentSymbol.Name = "a2" }

        // We have to check for reference equality here
        test <@ not <| obj.ReferenceEquals(resolver.ResolveSubcomponent field1, resolver.ResolveSubcomponent field2) @>

[<TestFixture>]
module ``ResolveMethod method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        let resolver = compile "class A : Component {} class B : Component {}"
        raisesArgumentNullException "methodSymbol" <@ resolver.ResolveMethod null @>

    [<Test>]
    let ``throws when method of non-component is passed`` () =
        let compilation = TestCompilation "class A : Component {} class B { void M() {} }"
        let methodSymbol = compilation.FindMethodSymbol "B" "M"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        raisesArgumentException "methodSymbol" <@ resolver.ResolveMethod methodSymbol @>

    [<Test>]
    let ``throws when constructor is passed`` () =
        let compilation = TestCompilation "class A : Component { int b; } class B : Component { }"
        let classSymbol = compilation.FindClassSymbol "A"
        let constructorSymbol = classSymbol.GetMembers().OfType<IMethodSymbol>().Single(fun method' -> method'.MethodKind = MethodKind.Constructor)
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        raisesArgumentException "methodSymbol" <@ resolver.ResolveMethod constructorSymbol @>

    [<Test>]
    let ``returns symbol for method of transformed component`` () =
        let compilation = TestCompilation "class A : Component { void M() {} } class B : Component {}"
        let methodSymbol = compilation.FindMethodSymbol "A" "M"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveMethod methodSymbol =? { MethodSymbol.Name = "M"; ReturnType = None; Parameters = [] }

    [<Test>]
    let ``returns update method symbol for update method of transformed component`` () =
        let compilation = TestCompilation "class A : Component { public override void Update() {} } class B : Component {}"
        let classSymbol = compilation.FindClassSymbol "A"
        let methodSymbol = compilation.FindMethodSymbol "A" "Update"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation
        let componentSymbol = resolver.ResolveComponent classSymbol

        resolver.ResolveMethod methodSymbol =? { MethodSymbol.Name = "Update"; ReturnType = None; Parameters = [] }

        // We have to check for reference equality here
        test <@ obj.ReferenceEquals(componentSymbol.UpdateMethod, resolver.ResolveMethod methodSymbol) @>

    [<Test>]
    let ``returns different symbols for different methods of same transformed component`` () =
        let compilation = TestCompilation "class A : Component { void M() {} void N() {} } class B : Component {}"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "A" "N"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveMethod method1 =? { MethodSymbol.Name = "M"; ReturnType = None; Parameters = [] }
        resolver.ResolveMethod method2 =? { MethodSymbol.Name = "N"; ReturnType = None; Parameters = [] }
        resolver.ResolveMethod method1 <>? resolver.ResolveMethod method2

    [<Test>]
    let ``returns different symbols for different methods of different transformed components`` () =
        let compilation = TestCompilation "class A : Component { void M() {} } class B : Component { void M() {} void N() {} }"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "B" "M"
        let method3 = compilation.FindMethodSymbol "B" "N"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveMethod method1 =? { MethodSymbol.Name = "M"; ReturnType = None; Parameters = [] }
        resolver.ResolveMethod method2 =? { MethodSymbol.Name = "M"; ReturnType = None; Parameters = [] }
        resolver.ResolveMethod method3 =? { MethodSymbol.Name = "N"; ReturnType = None; Parameters = [] }

        // We have to check for reference equality here
        test <@ not <| obj.ReferenceEquals(resolver.ResolveMethod method1, resolver.ResolveMethod method2) @>

[<TestFixture>]
module ``ResolveCSharpMethod method`` =
    [<Test>]
    let ``throws when method of non-component is passed`` () =
        let compilation = TestCompilation "class A : Component {} class B { void M() {} }"
        let methodSymbol = compilation.FindMethodSymbol "B" "M"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        raisesArgumentException "methodSymbol" <@ resolver.ResolveCSharpMethod <| resolver.ResolveMethod methodSymbol @> 

    [<Test>]
    let ``throws for update method of component that doesn't override it`` () =
        let compilation = TestCompilation "class A : Component {}"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        raisesArgumentException "methodSymbol" <@ resolver.ResolveCSharpMethod <| resolver.ComponentSymbols.[0].UpdateMethod @> 

    [<Test>]
    let ``returns symbol for method of transformed component`` () =
        let compilation = TestCompilation "class A : Component { void M() {} } class B : Component {}"
        let methodSymbol = compilation.FindMethodSymbol "A" "M"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveMethod methodSymbol |> resolver.ResolveCSharpMethod =? methodSymbol

    [<Test>]
    let ``returns update method symbol for update method of transformed component`` () =
        let compilation = TestCompilation "class A : Component { public override void Update() {} } class B : Component {}"
        let classSymbol = compilation.FindClassSymbol "A"
        let methodSymbol = compilation.FindMethodSymbol "A" "Update"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation
        let componentSymbol = resolver.ResolveComponent classSymbol

        resolver.ResolveMethod methodSymbol |> resolver.ResolveCSharpMethod =? methodSymbol
        resolver.ResolveCSharpMethod componentSymbol.UpdateMethod =? methodSymbol

    [<Test>]
    let ``returns different symbols for different methods of same transformed component`` () =
        let compilation = TestCompilation "class A : Component { void M() {} void N() {} } class B : Component {}"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "A" "N"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveMethod method1 |> resolver.ResolveCSharpMethod =? method1
        resolver.ResolveMethod method2 |> resolver.ResolveCSharpMethod =? method2

    [<Test>]
    let ``returns different symbols for different methods of different transformed components`` () =
        let compilation = TestCompilation "class A : Component { void M() {} } class B : Component { void M() {} void N() {} }"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "B" "M"
        let method3 = compilation.FindMethodSymbol "B" "N"
        let resolver = SymbolTransformation.Transform compilation.CSharpCompilation

        resolver.ResolveMethod method1 |> resolver.ResolveCSharpMethod =? method1
        resolver.ResolveMethod method2 |> resolver.ResolveCSharpMethod =? method2
        resolver.ResolveMethod method3 |> resolver.ResolveCSharpMethod =? method3

