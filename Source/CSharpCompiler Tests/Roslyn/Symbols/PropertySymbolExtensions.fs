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

namespace Roslyn.Symbols.PropertySymbolExtensions

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Tests
open SafetySharp.CSharpCompiler.Roslyn.Symbols
open SafetySharp.Modeling

[<TestFixture>]
module ``Overrides method`` =
    let overrides csharpCode propertyName =
        let compilation = TestCompilation ("class Y { public virtual int M { get; set; } public virtual int N { get; set; } }" + csharpCode)
        let propertySymbol = compilation.FindPropertySymbol "X" propertyName
        let overridenPropertySymbol = compilation.FindPropertySymbol "Y" "M"

        propertySymbol.Overrides overridenPropertySymbol

    [<Test>]
    let ``throws when property symbol is null`` () =
        let compilation = TestCompilation "class X { int P { get; set; } }"
        let propertySymbol = compilation.FindPropertySymbol "X" "P"
        raisesArgumentNullException "propertySymbol" (fun () -> (null : IPropertySymbol).Overrides propertySymbol |> ignore)

    [<Test>]
    let ``throws when overriden property symbol is null`` () =
        let compilation = TestCompilation "class X { int P { get; set; } }"
        let propertySymbol = compilation.FindPropertySymbol "X" "P"
        raisesArgumentNullException "overriddenProperty" (fun () -> propertySymbol.Overrides null |> ignore)

    [<Test>]
    let ``returns false for non-overriding property`` () =
        overrides "class X : Y { public int M { get; set; } }" "M" =? false
        overrides "class X : Y { public virtual int M { get; set; } }" "M" =? false
        overrides "class X : Y { public virtual int N { get; set; } }" "N" =? false
        overrides "class X { public virtual int M { get; set; } }" "M" =? false

    [<Test>]
    let ``returns true for overriding property`` () =
        overrides "class X : Y { public override int M { get; set; } }" "M" =? true
        overrides "class X : Y { public sealed override int M { get; set; } }" "M" =? true
        overrides "class Z : Y {} class X : Z { public override int M { get; set; } }" "M" =? true
        overrides "class Z : Y { public override int M { get; set; } } class X : Z { public override int M { get; set; } }" "M" =? true

    [<Test>]
    let ``returns true for the virtual property itself`` () =
        let compilation = TestCompilation "class Y { public virtual int M { get; set; } }"
        let propertySymbol = compilation.FindPropertySymbol "Y" "M"

        propertySymbol.Overrides propertySymbol =? true

//[<TestFixture>]
//module ``HasAttribute method`` =
//    let hasAttribute<'T when 'T :> Attribute> csharpCode =
//        let compilation = TestCompilation csharpCode
//        let propertySymbol = compilation.FindPropertySymbol "C" "P"
//        propertySymbol.HasAttribute<'T> compilation.CSharpCompilation
//
//    [<Test>]
//    let ``throws when compilation is null`` () =
//        let compilation = TestCompilation "class C { int P { get; set; }}"
//        let propertySymbol = compilation.FindPropertySymbol "C" "P"
//        raisesArgumentNullException "compilation" (fun () -> propertySymbol.HasAttribute<ProvidedAttribute> null |> ignore)
//
//    [<Test>]
//    let ``returns false if property has no attribute`` () =
//        hasAttribute<ProvidedAttribute> "class C { int P { get; set; }}" =? false
//
//    [<Test>]
//    let ``returns false if property has different attribute`` () =
//        hasAttribute<ProvidedAttribute> "class C { [Required] int P { get; set; }}" =? false
//
//    [<Test>]
//    let ``returns true if property has attribute`` () =
//        hasAttribute<ProvidedAttribute> "class C { [Provided] int P { get; set; }}" =? true