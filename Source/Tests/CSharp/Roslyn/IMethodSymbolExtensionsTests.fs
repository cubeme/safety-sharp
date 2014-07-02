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

namespace SafetySharp.Tests.CSharp.Roslyn.IMethodSymbolExtensionsTests

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Internal.CSharp
open SafetySharp.Tests
open SafetySharp.Internal.CSharp.Roslyn

[<TestFixture>]
module ``Overrides method`` =
    let overrides csharpCode methodName =
        let compilation = TestCompilation ("class Y { public virtual void M() {} public virtual void N() {} }" + csharpCode)
        let methodSymbol = compilation.FindMethodSymbol "X" methodName
        let overridenMethodSymbol = compilation.FindMethodSymbol "Y" "M"

        methodSymbol.Overrides overridenMethodSymbol

    [<Test>]
    let ``throws when overriden method symbol is null`` () =
        let compilation = TestCompilation "class X { void M() {} }"
        let methodSymbol = compilation.FindMethodSymbol "X" "M"
        raisesArgumentNullException "overriddenMethod" (fun () -> methodSymbol.Overrides null |> ignore)

    [<Test>]
    let ``returns false for non-overriding method`` () =
        overrides "class X : Y { public void M() {} }" "M" =? false
        overrides "class X : Y { public virtual void M() {} }" "M" =? false
        overrides "class X : Y { public virtual void N() {} }" "N" =? false
        overrides "class X { public virtual void M() {} }" "M" =? false

    [<Test>]
    let ``returns true for overriding method`` () =
        overrides "class X : Y { public override void M() {} }" "M" =? true
        overrides "class X : Y { public sealed override void M() {} }" "M" =? true
        overrides "class Z : Y {} class X : Z { public override void M () {} }" "M" =? true
        overrides "class Z : Y { public override void M() {} } class X : Z { public override void M () {} }" "M" =? true

    [<Test>]
    let ``returns true for the virtual method itself`` () =
        let compilation = TestCompilation "class Y { public virtual void M() {} }"
        let methodSymbol = compilation.FindMethodSymbol "Y" "M"

        methodSymbol.Overrides methodSymbol =? true

[<TestFixture>]
module ``IsUpdateMethod method`` =
    let isUpdateMethod csharpCode methodName =
        let compilation = TestCompilation csharpCode
        let methodSymbol = compilation.FindMethodSymbol "X" methodName
        methodSymbol.IsUpdateMethod compilation.SemanticModel
    
    [<Test>]
    let ``throws when semantic model is null`` () =
        let compilation = TestCompilation "class X { void M() {} }"
        let methodSymbol = compilation.FindMethodSymbol "X" "M"
        raisesArgumentNullException "semanticModel" (fun () -> methodSymbol.IsUpdateMethod (null : SemanticModel) |> ignore)

    [<Test>]
    let ``returns true for Update method of component`` () =
        isUpdateMethod "class X : Component { [Behavior] void Update() {} }" "Update" =? true

    [<Test>]
    let ``returns true for Update method of inherited component`` () =
        isUpdateMethod "class Y : Component {} class X : Y { [Behavior] void Update() {} }" "Update" =? true
        isUpdateMethod "class Y : Component { [Behavior] void Update() {} } class X : Y { [Behavior] void Update() {} }" "Update" =? true

    [<Test>]
    let ``returns false for non-overriding methods of component`` () =
        isUpdateMethod "class X : Component { void M() {} }" "M" =? false
        isUpdateMethod "class X : Component { public void Update() {} }" "Update" =? false

    [<Test>]
    let ``returns false for Update method of non-Component class`` () =
        isUpdateMethod "class X { public void Update() {} }" "Update" =? false

[<TestFixture>]
module ``GetMethodDeclaration method`` =

    let mutable private compilation : TestCompilation = null

    let getMethodDeclaration csharpCode className methodName =
        compilation <- TestCompilation csharpCode
        let methodSymbol = compilation.FindMethodSymbol className methodName
        methodSymbol.GetMethodDeclaration ()

    [<Test>]
    let ``returns method declaration of method defined in source at one location`` () =
        getMethodDeclaration "class C { void M() { return; }}" "C" "M" =? compilation.FindMethodDeclaration "C" "M"

    [<Test>]
    let ``throws when method is not defined in source`` () =
        raises<InvalidOperationException> (fun () -> getMethodDeclaration "" "System.Object" "ToString" |> ignore)