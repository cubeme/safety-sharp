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
    let compile csharpCode =
        let compilation = TestCompilation csharpCode
        SymbolTransformation.Transform compilation.CSharpCompilation

    let components csharpCode =
        let symbolMap = compile csharpCode
        symbolMap.Components

    let emptyUpdate = { Name = "Update"; ReturnType = None; Parameters = [] }
    let emptyComponent name = { Name = "TestCompilation::" + name; UpdateMethod = emptyUpdate; Fields = []; Methods = []; Subcomponents = [] } 

[<TestFixture>]
module ``Components property`` =
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
module ``ResolveComponent method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        let symbolMap = compile "class A : Component {} class B : Component {}"
        raisesWith<ArgumentNullException> <@ symbolMap.ResolveComponent null @> (fun e -> <@ e.ParamName = "componentSymbol" @>)

    [<Test>]
    let ``throws when non-component is passed`` () =
        let compilation = TestCompilation "class A : Component {} class B {}"
        let classB = compilation.FindClassSymbol "B"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        raises<InvalidOperationException> <@ symbolMap.ResolveComponent classB @>

    [<Test>]
    let ``returns symbol for transformed component`` () =
        let compilation = TestCompilation "class A : Component {} class B : Component {}"
        let classA = compilation.FindClassSymbol "A"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        symbolMap.ResolveComponent classA =? emptyComponent "A"

    [<Test>]
    let ``returns different symbols for different transformed components`` () =
        let compilation = TestCompilation "class A : Component {} class B : Component {}"
        let classA = compilation.FindClassSymbol "A"
        let classB = compilation.FindClassSymbol "B"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        symbolMap.ResolveComponent classA =? emptyComponent "A"
        symbolMap.ResolveComponent classB =? emptyComponent "B"
        symbolMap.ResolveComponent classA <>? symbolMap.ResolveComponent classB

[<TestFixture>]
module ``ResolveField method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        let symbolMap = compile "class A : Component {} class B : Component {}"
        raisesWith<ArgumentNullException> <@ symbolMap.ResolveField null @> (fun e -> <@ e.ParamName = "fieldSymbol" @>)

    [<Test>]
    let ``throws when field of non-component is passed`` () =
        let compilation = TestCompilation "class A : Component {} class B { int f; }"
        let field = compilation.FindFieldSymbol "B" "f"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        raises<InvalidOperationException> <@ symbolMap.ResolveField field @>

    [<Test>]
    let ``throws when subcomponent field is passed`` () =
        let compilation = TestCompilation "class A : Component { B b; } class B : Component { }"
        let field = compilation.FindFieldSymbol "A" "b"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        raises<InvalidOperationException> <@ symbolMap.ResolveField field @>

    [<Test>]
    let ``returns symbol for field of transformed component`` () =
        let compilation = TestCompilation "class A : Component { int f; } class B : Component {}"
        let field = compilation.FindFieldSymbol "A" "f"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        symbolMap.ResolveField field =? { FieldSymbol.Name = "f"; Type = TypeSymbol.Integer }

    [<Test>]
    let ``returns different symbols for different fields of same transformed component`` () =
        let compilation = TestCompilation "class A : Component { int f; bool g; } class B : Component {}"
        let field1 = compilation.FindFieldSymbol "A" "f"
        let field2 = compilation.FindFieldSymbol "A" "g"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        symbolMap.ResolveField field1 =? { FieldSymbol.Name = "f"; Type = TypeSymbol.Integer }
        symbolMap.ResolveField field2 =? { FieldSymbol.Name = "g"; Type = TypeSymbol.Boolean }
        symbolMap.ResolveField field1 <>? symbolMap.ResolveField field2

    [<Test>]
    let ``returns different symbols for different fields of different transformed components`` () =
        let compilation = TestCompilation "class A : Component { int f; } class B : Component { int f; int g; }"
        let field1 = compilation.FindFieldSymbol "A" "f"
        let field2 = compilation.FindFieldSymbol "B" "f"
        let field3 = compilation.FindFieldSymbol "B" "g"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        symbolMap.ResolveField field1 =? { FieldSymbol.Name = "f"; Type = TypeSymbol.Integer }
        symbolMap.ResolveField field2 =? { FieldSymbol.Name = "f"; Type = TypeSymbol.Integer }
        symbolMap.ResolveField field3 =? { FieldSymbol.Name = "g"; Type = TypeSymbol.Integer }

        // We have to check for reference equality here
        test <@ not <| obj.ReferenceEquals(symbolMap.ResolveField field1, symbolMap.ResolveField field2) @>

[<TestFixture>]
module ``ResolveSubcomponent method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        let symbolMap = compile "class A : Component {} class B : Component {}"
        raisesWith<ArgumentNullException> <@ symbolMap.ResolveSubcomponent null @> (fun e -> <@ e.ParamName = "subcomponentSymbol" @>)

    [<Test>]
    let ``throws when subcomponent of non-component is passed`` () =
        let compilation = TestCompilation "class A : Component {} class B { A f; }"
        let field = compilation.FindFieldSymbol "B" "f"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        raises<InvalidOperationException> <@ symbolMap.ResolveSubcomponent field @>

    [<Test>]
    let ``throws when non-subcomponent field is passed`` () =
        let compilation = TestCompilation "class A : Component { int b; } class B : Component { }"
        let field = compilation.FindFieldSymbol "A" "b"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        raises<InvalidOperationException> <@ symbolMap.ResolveSubcomponent field @>

    [<Test>]
    let ``returns symbol for subcomponent of transformed component`` () =
        let compilation = TestCompilation "class A : Component { B f; } class B : Component {}"
        let field = compilation.FindFieldSymbol "A" "f"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        symbolMap.ResolveSubcomponent field =? { SubcomponentSymbol.Name = "f" }

    [<Test>]
    let ``returns different symbols for different subcomponents of same transformed component`` () =
        let compilation = TestCompilation "class A : Component { B b1; B b2; } class B : Component {}"
        let field1 = compilation.FindFieldSymbol "A" "b1"
        let field2 = compilation.FindFieldSymbol "A" "b2"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        symbolMap.ResolveSubcomponent field1 =? { SubcomponentSymbol.Name = "b1" }
        symbolMap.ResolveSubcomponent field2 =? { SubcomponentSymbol.Name = "b2" }
        symbolMap.ResolveSubcomponent field1 <>? symbolMap.ResolveSubcomponent field2

    [<Test>]
    let ``returns different symbols for different subcomponents of different transformed components`` () =
        let compilation = TestCompilation "class A : Component { B b; } class B : Component { A a1; A a2; }"
        let field1 = compilation.FindFieldSymbol "A" "b"
        let field2 = compilation.FindFieldSymbol "B" "a1"
        let field3 = compilation.FindFieldSymbol "B" "a2"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        symbolMap.ResolveSubcomponent field1 =? { SubcomponentSymbol.Name = "b" }
        symbolMap.ResolveSubcomponent field2 =? { SubcomponentSymbol.Name = "a1" }
        symbolMap.ResolveSubcomponent field3 =? { SubcomponentSymbol.Name = "a2" }

        // We have to check for reference equality here
        test <@ not <| obj.ReferenceEquals(symbolMap.ResolveSubcomponent field1, symbolMap.ResolveSubcomponent field2) @>

[<TestFixture>]
module ``ResolveMethod method`` =
    [<Test>]
    let ``throws when null is passed`` () =
        let symbolMap = compile "class A : Component {} class B : Component {}"
        raisesWith<ArgumentNullException> <@ symbolMap.ResolveMethod null @> (fun e -> <@ e.ParamName = "methodSymbol" @>)

    [<Test>]
    let ``throws when method of non-component is passed`` () =
        let compilation = TestCompilation "class A : Component {} class B { void M() {} }"
        let methodSymbol = compilation.FindMethodSymbol "B" "M"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        raises<InvalidOperationException> <@ symbolMap.ResolveMethod methodSymbol @>

    [<Test>]
    let ``throws when constructor is passed`` () =
        let compilation = TestCompilation "class A : Component { int b; } class B : Component { }"
        let classSymbol = compilation.FindClassSymbol "A"
        let constructorSymbol = classSymbol.GetMembers().OfType<IMethodSymbol>().Single(fun method' -> method'.MethodKind = MethodKind.Constructor)
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        raises<InvalidOperationException> <@ symbolMap.ResolveMethod constructorSymbol @>

    [<Test>]
    let ``returns symbol for method of transformed component`` () =
        let compilation = TestCompilation "class A : Component { void M() {} } class B : Component {}"
        let methodSymbol = compilation.FindMethodSymbol "A" "M"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        symbolMap.ResolveMethod methodSymbol =? { MethodSymbol.Name = "M"; ReturnType = None; Parameters = [] }

    [<Test>]
    let ``returns update method symbol for update method of transformed component`` () =
        let compilation = TestCompilation "class A : Component { public override void Update() {} } class B : Component {}"
        let classSymbol = compilation.FindClassSymbol "A"
        let methodSymbol = compilation.FindMethodSymbol "A" "Update"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation
        let componentSymbol = symbolMap.ResolveComponent classSymbol

        symbolMap.ResolveMethod methodSymbol =? { MethodSymbol.Name = "Update"; ReturnType = None; Parameters = [] }

        // We have to check for reference equality here
        test <@ obj.ReferenceEquals(componentSymbol.UpdateMethod, symbolMap.ResolveMethod methodSymbol) @>

    [<Test>]
    let ``returns different symbols for different methods of same transformed component`` () =
        let compilation = TestCompilation "class A : Component { void M() {} void N() {} } class B : Component {}"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "A" "N"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        symbolMap.ResolveMethod method1 =? { MethodSymbol.Name = "M"; ReturnType = None; Parameters = [] }
        symbolMap.ResolveMethod method2 =? { MethodSymbol.Name = "N"; ReturnType = None; Parameters = [] }
        symbolMap.ResolveMethod method1 <>? symbolMap.ResolveMethod method2

    [<Test>]
    let ``returns different symbols for different methods of different transformed components`` () =
        let compilation = TestCompilation "class A : Component { void M() {} } class B : Component { void M() {} void N() {} }"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "B" "M"
        let method3 = compilation.FindMethodSymbol "B" "N"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        symbolMap.ResolveMethod method1 =? { MethodSymbol.Name = "M"; ReturnType = None; Parameters = [] }
        symbolMap.ResolveMethod method2 =? { MethodSymbol.Name = "M"; ReturnType = None; Parameters = [] }
        symbolMap.ResolveMethod method3 =? { MethodSymbol.Name = "N"; ReturnType = None; Parameters = [] }

        // We have to check for reference equality here
        test <@ not <| obj.ReferenceEquals(symbolMap.ResolveMethod method1, symbolMap.ResolveMethod method2) @>

[<TestFixture>]
module ``ResolveCSharpMethod method`` =
    [<Test>]
    let ``throws when method of non-component is passed`` () =
        let compilation = TestCompilation "class A : Component {} class B { void M() {} }"
        let methodSymbol = compilation.FindMethodSymbol "B" "M"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        raises<InvalidOperationException> <@ symbolMap.ResolveCSharpMethod <| symbolMap.ResolveMethod methodSymbol @>

    [<Test>]
    let ``throws for update method of component that doesn't override it`` () =
        let compilation = TestCompilation "class A : Component {}"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        raises<InvalidOperationException> <@ symbolMap.ResolveCSharpMethod <| symbolMap.Components.[0].UpdateMethod @>

    [<Test>]
    let ``returns symbol for method of transformed component`` () =
        let compilation = TestCompilation "class A : Component { void M() {} } class B : Component {}"
        let methodSymbol = compilation.FindMethodSymbol "A" "M"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        symbolMap.ResolveMethod methodSymbol |> symbolMap.ResolveCSharpMethod =? methodSymbol

    [<Test>]
    let ``returns update method symbol for update method of transformed component`` () =
        let compilation = TestCompilation "class A : Component { public override void Update() {} } class B : Component {}"
        let classSymbol = compilation.FindClassSymbol "A"
        let methodSymbol = compilation.FindMethodSymbol "A" "Update"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation
        let componentSymbol = symbolMap.ResolveComponent classSymbol

        symbolMap.ResolveMethod methodSymbol |> symbolMap.ResolveCSharpMethod =? methodSymbol
        symbolMap.ResolveCSharpMethod componentSymbol.UpdateMethod =? methodSymbol

    [<Test>]
    let ``returns different symbols for different methods of same transformed component`` () =
        let compilation = TestCompilation "class A : Component { void M() {} void N() {} } class B : Component {}"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "A" "N"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        symbolMap.ResolveMethod method1 |> symbolMap.ResolveCSharpMethod =? method1
        symbolMap.ResolveMethod method2 |> symbolMap.ResolveCSharpMethod =? method2

    [<Test>]
    let ``returns different symbols for different methods of different transformed components`` () =
        let compilation = TestCompilation "class A : Component { void M() {} } class B : Component { void M() {} void N() {} }"
        let method1 = compilation.FindMethodSymbol "A" "M"
        let method2 = compilation.FindMethodSymbol "B" "M"
        let method3 = compilation.FindMethodSymbol "B" "N"
        let symbolMap = SymbolTransformation.Transform compilation.CSharpCompilation

        symbolMap.ResolveMethod method1 |> symbolMap.ResolveCSharpMethod =? method1
        symbolMap.ResolveMethod method2 |> symbolMap.ResolveCSharpMethod =? method2
        symbolMap.ResolveMethod method3 |> symbolMap.ResolveCSharpMethod =? method3

