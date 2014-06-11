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
open SafetySharp.Tests.CSharp

[<AutoOpen>]
module private SymbolTransformationTestsHelper =
    let compile csharpCode components =
        let compilation = TestCompilation csharpCode
        SymbolTransformation.Transform compilation.CSharpCompilation components

    let components csharpCode components =
        let symbolMap = compile csharpCode components
        symbolMap.Components

    let emptyUpdate = { Name = "Update"; ReturnType = None; Parameters = [] }
    let emptyComponent name = { Name = "TestCompilation::" + name; UpdateMethod = emptyUpdate; Fields = []; Methods = []; Subcomponents = [] } 

[<TestFixture>]
module TransformMethod =
    [<Test>]
    let ``throws when no components are provided`` () =
        raises<ArgumentException> <@ compile "class C : Component {}" [] @>

    [<Test>]
    let ``throws when non-component is provided`` () =
        raises<InvalidOperationException> <@ compile "class C {}" ["C"] @>

    [<Test>]
    let ``throws when provided component cannot be found`` () =
        raises<InvalidOperationException> <@ compile "class C : Component {}" ["A"] @>

[<TestFixture>]
module ComponentsProperty =
    [<Test>]
    let ``contains all components`` () =
        components "class A : Component {} class B : Component {} class C : Component {}" ["A"; "B"; "C"]
        =? [ emptyComponent "A"; emptyComponent "B"; emptyComponent "C" ]

    [<Test>]
    let ``does not contain ignored components`` () =
        components "class A : Component {} class B : Component {} class C : Component {}" ["A"; "C"]
        =? [ emptyComponent "A"; emptyComponent "C" ]

    [<Test>]
    let ``contains components that are provided multiple times only once`` () =
        components "class A : Component {} class B : Component {} class C : Component {}" ["C"; "A"; "C"]
        =? [ emptyComponent "C"; emptyComponent "A" ]

    [<Test>]
    let ``component name contains namespaces and nested types`` () =
        let transformedComponents = components "namespace Test { class A : Component { } }" ["Test.A"]
        transformedComponents.[0] =? emptyComponent "Test.A"

        let transformedComponents = components "namespace Test1 { namespace Test2 { class A : Component { } }}" ["Test1.Test2.A"]
        transformedComponents.[0] =? emptyComponent "Test1.Test2.A"

        let transformedComponents = components "namespace Test1.Test2 { class A : Component { } }" ["Test1.Test2.A"]
        transformedComponents.[0] =? emptyComponent "Test1.Test2.A"

        let transformedComponents = components "namespace Test { class Nested { class A : Component { } }}" ["Test.Nested+A"]
        transformedComponents.[0] =? emptyComponent "Test.Nested.A"

    [<Test>]
    let ``component symbol contains all fields`` () =
        let components = components "class A : Component { int i; bool b; decimal d; }" ["A"]
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
        let components = components "class A : Component { Component c; B b; IComponent i; } class B : Component {}" ["A"; "B"]
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
        let components = components "class A : Component { int M(int i, decimal d) { return 0; } void N(bool b) {} bool O() { return false; } }" ["A"]
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
        let components = components "class A : Component { public override void Update() {} }" ["A"]
        components.[0] =? { emptyComponent "A" with UpdateMethod = { MethodSymbol.Name = "Update"; ReturnType = None; Parameters = [] } }

    [<Test>]
    let ``component symbol contains all data`` () =
        let components = components "class C : Component { bool N(int x) { return false; } public override void Update() {} int f; IComponent c; }" ["C"]
        components.[0] =? {
            emptyComponent "C" with
                Methods = [{ MethodSymbol.Name = "N"; ReturnType = Some TypeSymbol.Boolean; Parameters = [{ ParameterSymbol.Name = "x"; Type = TypeSymbol.Integer }] }]
                Fields = [{ FieldSymbol.Name = "f"; Type = TypeSymbol.Integer }]
                Subcomponents = [{ SubcomponentSymbol.Name = "c" }]
                UpdateMethod = { MethodSymbol.Name = "Update"; ReturnType = None; Parameters = [] }
        }

[<TestFixture>]
module ResolveComponentMethod =
    [<Test>]
    let ``throws when null is passed`` () =
        let symbolMap = compile "class A : Component {} class B : Component {}" ["A"]
        raises<ArgumentNullException> <@ symbolMap.ResolveComponent null @>

    [<Test>]
    let ``throws when non-transformed component is passed`` () =
        let compilation = TestCompilation "class A : Component {} class B : Component {}"
        let classB = compilation.FindClassSymbol "B"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"]

        raises<InvalidOperationException> <@ symbolMap.ResolveComponent classB @>

    [<Test>]
    let ``returns symbol for transformed component`` () =
        let compilation = TestCompilation "class A : Component {} class B : Component {}"
        let classA = compilation.FindClassSymbol "A"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"]

        symbolMap.ResolveComponent classA =? emptyComponent "A"

    [<Test>]
    let ``returns different symbols for different transformed components`` () =
        let compilation = TestCompilation "class A : Component {} class B : Component {}"
        let classA = compilation.FindClassSymbol "A"
        let classB = compilation.FindClassSymbol "B"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"; "B"]

        symbolMap.ResolveComponent classA =? emptyComponent "A"
        symbolMap.ResolveComponent classB =? emptyComponent "B"
        symbolMap.ResolveComponent classA <>? symbolMap.ResolveComponent classB

[<TestFixture>]
module ResolveFieldMethod =
    [<Test>]
    let ``throws when null is passed`` () =
        let symbolMap = compile "class A : Component {} class B : Component {}" ["A"]
        raises<ArgumentNullException> <@ symbolMap.ResolveField null @>

    [<Test>]
    let ``throws when field of non-transformed component is passed`` () =
        let compilation = TestCompilation "class A : Component {} class B : Component { int f; }"
        let field = compilation.FindFieldSymbol "B" "f"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"]

        raises<InvalidOperationException> <@ symbolMap.ResolveField field @>

    [<Test>]
    let ``throws when subcomponent field is passed`` () =
        let compilation = TestCompilation "class A : Component { B b; } class B : Component { }"
        let field = compilation.FindFieldSymbol "A" "b"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"; "B"]

        raises<InvalidOperationException> <@ symbolMap.ResolveField field @>

    [<Test>]
    let ``returns symbol for field of transformed component`` () =
        let compilation = TestCompilation "class A : Component { int f; } class B : Component {}"
        let field = compilation.FindFieldSymbol "A" "f"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"]

        symbolMap.ResolveField field =? { FieldSymbol.Name = "f"; Type = TypeSymbol.Integer }

    [<Test>]
    let ``returns different symbols for different fields of same transformed component`` () =
        let compilation = TestCompilation "class A : Component { int f; bool g; } class B : Component {}"
        let field1 = compilation.FindFieldSymbol "A" "f"
        let field2 = compilation.FindFieldSymbol "A" "g"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"; "B"]

        symbolMap.ResolveField field1 =? { FieldSymbol.Name = "f"; Type = TypeSymbol.Integer }
        symbolMap.ResolveField field2 =? { FieldSymbol.Name = "g"; Type = TypeSymbol.Boolean }
        symbolMap.ResolveField field1 <>? symbolMap.ResolveField field2

    [<Test>]
    let ``returns different symbols for different fields of different transformed components`` () =
        let compilation = TestCompilation "class A : Component { int f; } class B : Component { int f; int g; }"
        let field1 = compilation.FindFieldSymbol "A" "f"
        let field2 = compilation.FindFieldSymbol "B" "f"
        let field3 = compilation.FindFieldSymbol "B" "g"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"; "B"]

        symbolMap.ResolveField field1 =? { FieldSymbol.Name = "f"; Type = TypeSymbol.Integer }
        symbolMap.ResolveField field2 =? { FieldSymbol.Name = "f"; Type = TypeSymbol.Integer }
        symbolMap.ResolveField field3 =? { FieldSymbol.Name = "g"; Type = TypeSymbol.Integer }

        // We have to check for reference equality here
        test <@ not <| obj.ReferenceEquals(symbolMap.ResolveField field1, symbolMap.ResolveField field2) @>

[<TestFixture>]
module ResolveSubcomponentMethod =
    [<Test>]
    let ``throws when null is passed`` () =
        let symbolMap = compile "class A : Component {} class B : Component {}" ["A"]
        raises<ArgumentNullException> <@ symbolMap.ResolveSubcomponent null @>

    [<Test>]
    let ``throws when subcomponent of non-transformed component is passed`` () =
        let compilation = TestCompilation "class A : Component {} class B : Component { A f; }"
        let field = compilation.FindFieldSymbol "B" "f"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"]

        raises<InvalidOperationException> <@ symbolMap.ResolveSubcomponent field @>

    [<Test>]
    let ``throws when non-subcomponent field is passed`` () =
        let compilation = TestCompilation "class A : Component { int b; } class B : Component { }"
        let field = compilation.FindFieldSymbol "A" "b"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"; "B"]

        raises<InvalidOperationException> <@ symbolMap.ResolveSubcomponent field @>

    [<Test>]
    let ``returns symbol for subcomponent of transformed component`` () =
        let compilation = TestCompilation "class A : Component { B f; } class B : Component {}"
        let field = compilation.FindFieldSymbol "A" "f"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"]

        symbolMap.ResolveSubcomponent field =? { SubcomponentSymbol.Name = "f" }

    [<Test>]
    let ``returns different symbols for different subcomponents of same transformed component`` () =
        let compilation = TestCompilation "class A : Component { B b1; B b2; } class B : Component {}"
        let field1 = compilation.FindFieldSymbol "A" "b1"
        let field2 = compilation.FindFieldSymbol "A" "b2"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"; "B"]

        symbolMap.ResolveSubcomponent field1 =? { SubcomponentSymbol.Name = "b1" }
        symbolMap.ResolveSubcomponent field2 =? { SubcomponentSymbol.Name = "b2" }
        symbolMap.ResolveSubcomponent field1 <>? symbolMap.ResolveSubcomponent field2

    [<Test>]
    let ``returns different symbols for different subcomponents of different transformed components`` () =
        let compilation = TestCompilation "class A : Component { B b; } class B : Component { A a1; A a2; }"
        let field1 = compilation.FindFieldSymbol "A" "b"
        let field2 = compilation.FindFieldSymbol "B" "a1"
        let field3 = compilation.FindFieldSymbol "B" "a2"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"; "B"]

        symbolMap.ResolveSubcomponent field1 =? { SubcomponentSymbol.Name = "b" }
        symbolMap.ResolveSubcomponent field2 =? { SubcomponentSymbol.Name = "a1" }
        symbolMap.ResolveSubcomponent field3 =? { SubcomponentSymbol.Name = "a2" }

        // We have to check for reference equality here
        test <@ not <| obj.ReferenceEquals(symbolMap.ResolveSubcomponent field1, symbolMap.ResolveSubcomponent field2) @>

[<TestFixture>]
module ResolveMethodMethod =
    [<Test>]
    let ``throws when null is passed`` () =
        let symbolMap = compile "class A : Component {} class B : Component {}" ["A"]
        raises<ArgumentNullException> <@ symbolMap.ResolveMethod null @>

    [<Test>]
    let ``throws when method of non-transformed component is passed`` () =
        let compilation = TestCompilation "class A : Component {} class B : Component { void M() {} }"
        let methodSymbol = compilation.FindMethodSymbol "B" "M"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"]

        raises<InvalidOperationException> <@ symbolMap.ResolveMethod methodSymbol @>

    [<Test>]
    let ``throws when constructor is passed`` () =
        let compilation = TestCompilation "class A : Component { int b; } class B : Component { }"
        let classSymbol = compilation.FindClassSymbol "A"
        let constructorSymbol = classSymbol.GetMembers().OfType<IMethodSymbol>().Single(fun method' -> method'.MethodKind = MethodKind.Constructor)
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"; "B"]

        raises<InvalidOperationException> <@ symbolMap.ResolveMethod constructorSymbol @>

    [<Test>]
    let ``returns symbol for method of transformed component`` () =
        let compilation = TestCompilation "class A : Component { void M() {} } class B : Component {}"
        let methodSymbol = compilation.FindMethodSymbol "A" "M"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"]

        symbolMap.ResolveMethod methodSymbol =? { MethodSymbol.Name = "M"; ReturnType = None; Parameters = [] }

    [<Test>]
    let ``returns update method symbol for update method of transformed component`` () =
        let compilation = TestCompilation "class A : Component { public override void Update() {} } class B : Component {}"
        let classSymbol = compilation.FindClassSymbol "A"
        let methodSymbol = compilation.FindMethodSymbol "A" "Update"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"]
        let componentSymbol = symbolMap.ResolveComponent classSymbol

        symbolMap.ResolveMethod methodSymbol =? { MethodSymbol.Name = "Update"; ReturnType = None; Parameters = [] }

        // We have to check for reference equality here
        test <@ obj.ReferenceEquals(componentSymbol.UpdateMethod, symbolMap.ResolveMethod methodSymbol) @>

    [<Test>]
    let ``returns different symbols for different methods of same transformed component`` () =
        let compilation = TestCompilation "class A : Component { void M() {} void N() {} } class B : Component {}"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "A" "N"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"; "B"]

        symbolMap.ResolveMethod method1 =? { MethodSymbol.Name = "M"; ReturnType = None; Parameters = [] }
        symbolMap.ResolveMethod method2 =? { MethodSymbol.Name = "N"; ReturnType = None; Parameters = [] }
        symbolMap.ResolveMethod method1 <>? symbolMap.ResolveMethod method2

    [<Test>]
    let ``returns different symbols for different methods of different transformed components`` () =
        let compilation = TestCompilation "class A : Component { void M() {} } class B : Component { void M() {} void N() {} }"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "B" "M"
        let method3 = compilation.FindMethodSymbol "B" "N"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"; "B"]

        symbolMap.ResolveMethod method1 =? { MethodSymbol.Name = "M"; ReturnType = None; Parameters = [] }
        symbolMap.ResolveMethod method2 =? { MethodSymbol.Name = "M"; ReturnType = None; Parameters = [] }
        symbolMap.ResolveMethod method3 =? { MethodSymbol.Name = "N"; ReturnType = None; Parameters = [] }

        // We have to check for reference equality here
        test <@ not <| obj.ReferenceEquals(symbolMap.ResolveMethod method1, symbolMap.ResolveMethod method2) @>

[<TestFixture>]
module ResolveCSharpMethodMethod =
    [<Test>]
    let ``throws when method of non-transformed component is passed`` () =
        let compilation = TestCompilation "class A : Component {} class B : Component { void M() {} }"
        let methodSymbol = compilation.FindMethodSymbol "B" "M"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"]

        raises<InvalidOperationException> <@ symbolMap.ResolveCSharpMethod <| symbolMap.ResolveMethod methodSymbol @>

    [<Test>]
    let ``throws for update method of component that doesn't override it`` () =
        let compilation = TestCompilation "class A : Component {}"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"]

        raises<InvalidOperationException> <@ symbolMap.ResolveCSharpMethod <| symbolMap.Components.[0].UpdateMethod @>

    [<Test>]
    let ``returns symbol for method of transformed component`` () =
        let compilation = TestCompilation "class A : Component { void M() {} } class B : Component {}"
        let methodSymbol = compilation.FindMethodSymbol "A" "M"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"]

        symbolMap.ResolveMethod methodSymbol |> symbolMap.ResolveCSharpMethod =? methodSymbol

    [<Test>]
    let ``returns update method symbol for update method of transformed component`` () =
        let compilation = TestCompilation "class A : Component { public override void Update() {} } class B : Component {}"
        let classSymbol = compilation.FindClassSymbol "A"
        let methodSymbol = compilation.FindMethodSymbol "A" "Update"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"]
        let componentSymbol = symbolMap.ResolveComponent classSymbol

        symbolMap.ResolveMethod methodSymbol |> symbolMap.ResolveCSharpMethod =? methodSymbol
        symbolMap.ResolveCSharpMethod componentSymbol.UpdateMethod =? methodSymbol

    [<Test>]
    let ``returns different symbols for different methods of same transformed component`` () =
        let compilation = TestCompilation "class A : Component { void M() {} void N() {} } class B : Component {}"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "A" "N"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"; "B"]

        symbolMap.ResolveMethod method1 |> symbolMap.ResolveCSharpMethod =? method1
        symbolMap.ResolveMethod method2 |> symbolMap.ResolveCSharpMethod =? method2

    [<Test>]
    let ``returns different symbols for different methods of different transformed components`` () =
        let compilation = TestCompilation "class A : Component { void M() {} } class B : Component { void M() {} void N() {} }"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "B" "M"
        let method3 = compilation.FindMethodSymbol "B" "N"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation ["A"; "B"]

        symbolMap.ResolveMethod method1 |> symbolMap.ResolveCSharpMethod =? method1
        symbolMap.ResolveMethod method2 |> symbolMap.ResolveCSharpMethod =? method2
        symbolMap.ResolveMethod method3 |> symbolMap.ResolveCSharpMethod =? method3

