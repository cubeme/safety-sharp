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

namespace Roslyn.Symbols.MethodSymbolExtensions

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp.Roslyn
open SafetySharp.CSharp.Roslyn.Symbols
open SafetySharp.Modeling

[<TestFixture>]
module ``Overrides method`` =
    let overrides csharpCode methodName =
        let compilation = TestCompilation ("class Y { public virtual void M() {} public virtual void N() {} }" + csharpCode)
        let methodSymbol = compilation.FindMethodSymbol "X" methodName
        let overridenMethodSymbol = compilation.FindMethodSymbol "Y" "M"

        methodSymbol.Overrides overridenMethodSymbol

    [<Test>]
    let ``throws when method symbol is null`` () =
        let compilation = TestCompilation "class X { void M() {} }"
        let methodSymbol = compilation.FindMethodSymbol "X" "M"
        raisesArgumentNullException "methodSymbol" (fun () -> (null : IMethodSymbol).Overrides methodSymbol |> ignore)

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
module ``IsUpdateMethod methods`` =
    let isUpdateMethod csharpCode methodName =
        let compilation = TestCompilation csharpCode
        let methodSymbol = compilation.FindMethodSymbol "X" methodName
        methodSymbol.IsUpdateMethod compilation.SemanticModel && methodSymbol.IsUpdateMethod compilation.CSharpCompilation

    [<Test>]
    let ``throws when method symbol is null`` () =
        let compilation = TestCompilation "class X { void M() {} }"
        raisesArgumentNullException "methodSymbol" (fun () -> (null : IMethodSymbol).IsUpdateMethod compilation.SemanticModel |> ignore)
    
    [<Test>]
    let ``throws when semantic model is null`` () =
        let compilation = TestCompilation "class X { void M() {} }"
        let methodSymbol = compilation.FindMethodSymbol "X" "M"
        raisesArgumentNullException "semanticModel" (fun () -> methodSymbol.IsUpdateMethod (null : SemanticModel) |> ignore)

    [<Test>]
    let ``throws when compilation is null`` () =
        let compilation = TestCompilation "class X { void M() {} }"
        let methodSymbol = compilation.FindMethodSymbol "X" "M"
        raisesArgumentNullException "compilation" (fun () -> methodSymbol.IsUpdateMethod (null : Compilation) |> ignore)

    [<Test>]
    let ``returns true for Update method within component`` () =
        isUpdateMethod "class X : Component { public override void Update() {} }" "Update" =? true

    [<Test>]
    let ``returns true for inherited Update methods within components`` () =
        isUpdateMethod "class Y : Component {} class X : Y { public override void Update() {} }" "Update" =? true
        isUpdateMethod "class Y : Component { public override void Update() {} } class X : Y { public override void Update() {} }" "Update" =? true

    [<Test>]
    let ``returns false for non-Update method within component`` () =
        isUpdateMethod "class X : Component { void M() {} }" "M" =? false

    [<Test>]
    let ``returns false for Update method outside of component`` () =
        isUpdateMethod "class Y { public virtual void Update() {} } class X : Y { public override void Update() {} }" "Update" =? false

[<TestFixture>]
module ``GetSynthesizedDelegateDeclaration method`` =
    let synthesize csharpCode methodName =
        let compilation = TestCompilation csharpCode
        let methodSymbol = compilation.FindMethodSymbol "X" methodName
        methodSymbol.GetSynthesizedDelegateDeclaration(IdentifierNameSynthesizer.ToSynthesizedName "D").ToString ()

    [<Test>]
    let ``throws when method symbol is null`` () =
        let compilation = TestCompilation "class X { void M() {} }"
        raisesArgumentNullException "methodSymbol" (fun () -> (null : IMethodSymbol).GetSynthesizedDelegateDeclaration "D" |> ignore)

    [<Test>]
    let ``throws when name is null`` () =
        let compilation = TestCompilation "class X { void M() {} }"
        let methodSymbol = compilation.FindMethodSymbol "X" "M"
        raisesArgumentNullException "name" (fun () -> methodSymbol.GetSynthesizedDelegateDeclaration null |> ignore)

    [<Test>]
    let ``returns delegate for 'void -> void' method`` () =
        synthesize "class X { void M() {} }" "M" =? 
            "private delegate void __D__();" 

    [<Test>]
    let ``returns delegate for 'bool, int' -> bool' method`` () =
        synthesize "class X { bool M(bool b, int i) { return b; } }" "M" =? 
            "private delegate bool __D__(bool b, int i);" 

    [<Test>]
    let ``returns delegate for 'double, params int[]' -> double' method`` () =
        synthesize "class X { double M(double d, params int[] i) { return d; } }" "M" =? 
            "private delegate double __D__(double d, params int[] i);" 

    [<Test>]
    let ``returns delegate for 'double, int[][]' -> double' method`` () =
        synthesize "class X { double M(double d, int[][] i) { return d; } }" "M" =? 
            "private delegate double __D__(double d, int[][] i);" 

    [<Test>]
    let ``returns delegate for 'Q.R<int> -> void' method`` () =
        synthesize "namespace Q { class R<T> {}} class X { void M(Q.R<int> r) {} }" "M" =? 
            "private delegate void __D__(Q.R<int> r);" 

    [<Test>]
    let ``returns delegate for 'Q.R<int>[] -> void' method`` () =
        synthesize "namespace Q { class R<T> {}} class X { void M(Q.R<int>[] r) {} }" "M" =? 
            "private delegate void __D__(Q.R<int>[] r);" 

    [<Test>]
    let ``returns delegate for 'ref int -> void' method`` () =
        synthesize "class X { void M(ref int i) {} }" "M" =? 
            "private delegate void __D__(ref int i);" 

    [<Test>]
    let ``returns delegate for 'out int -> void' method`` () =
        synthesize "class X { void M(out int i) { i = 0; } }" "M" =? 
            "private delegate void __D__(out int i);" 

    [<Test>]
    let ``returns delegate for explicitly implemented 'void -> void' interface method`` () =
        synthesize "namespace Q { interface I { void M(); }} class X : Q.I { void Q.I.M() { } }" "Q.I.M" =? 
            "private delegate void __D__();" 

    [<Test>]
    let ``returns delegate for property getter`` () =
        synthesize "class X { int M { get; set; } }" "get_M" =? 
            "private delegate int __D__();" 

    [<Test>]
    let ``returns delegate for property setter`` () =
        synthesize "class X { int M { get; set; } }" "set_M" =? 
            "private delegate void __D__(int value);" 