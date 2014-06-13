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

namespace SafetySharp.Tests.CSharp.Extensions.CompilationExtensionsTests

open System.Linq
open NUnit.Framework
open Swensen.Unquote
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp
open SafetySharp.Tests
open SafetySharp.CSharp.Extensions

[<TestFixture>]
module ``GetTypeSymbols method`` =
    let mutable private compilation = Unchecked.defaultof<TestCompilation>

    let getTypeSymbols csharpCode =
        compilation <- TestCompilation csharpCode
        compilation.CSharpCompilation.GetTypeSymbols () |> List.ofSeq

    let find typeName = compilation.FindTypeSymbol typeName

    [<Test>]
    let ``returns empty list when no types are defined`` () =
        getTypeSymbols "" =? []

    [<Test>]
    let ``returns class symbol for non-nested class`` () =
        getTypeSymbols "class X {}" =? [find "X"]

    [<Test>]
    let ``returns class symbol for class nested in namespace`` () =
        getTypeSymbols "namespace Y.Z { class X {}}" =? [find "Y.Z.X"]

    [<Test>]
    let ``returns class symbol for class nested in other type`` () =
        getTypeSymbols "namespace Y.Z { class W { class X {}}}" =? [find "Y.Z.W"; find "Y.Z.W+X"]
        getTypeSymbols "namespace Y.Z { struct W { class X {}}}" =? [find "Y.Z.W"; find "Y.Z.W+X"]

    [<Test>]
    let ``returns struct symbol for non-nested struct`` () =
        getTypeSymbols "struct X {}" =? [find "X"]

    [<Test>]
    let ``returns struct symbol for struct nested in namespace`` () =
        getTypeSymbols "namespace Y.Z { struct X {}}" =? [find "Y.Z.X"]

    [<Test>]
    let ``returns struct symbol for struct nested in other type`` () =
        getTypeSymbols "namespace Y.Z { class W { struct X {}}}" =? [find "Y.Z.W"; find "Y.Z.W+X"]
        getTypeSymbols "namespace Y.Z { struct W { struct X {}}}" =? [find "Y.Z.W"; find "Y.Z.W+X"]

    [<Test>]
    let ``returns interface symbol for non-nested interface`` () =
        getTypeSymbols "interface X {}" =? [find "X"]

    [<Test>]
    let ``returns interface symbol for interface nested in namespace`` () =
        getTypeSymbols "namespace Y.Z { interface X {}}" =? [find "Y.Z.X"]

    [<Test>]
    let ``returns interface symbol for interface nested in other type`` () =
        getTypeSymbols "namespace Y.Z { class W { interface X {}}}" =? [find "Y.Z.W"; find "Y.Z.W+X"]
        getTypeSymbols "namespace Y.Z { struct W { interface X {}}}" =? [find "Y.Z.W"; find "Y.Z.W+X"]

    [<Test>]
    let ``returns enum symbol for non-nested enum`` () =
        getTypeSymbols "enum X {}" =? [find "X"]

    [<Test>]
    let ``returns enum symbol for enum nested in namespace`` () =
        getTypeSymbols "namespace Y.Z { enum X {}}" =? [find "Y.Z.X"]

    [<Test>]
    let ``returns enum symbol for enum nested in other type`` () =
        getTypeSymbols "namespace Y.Z { class W { enum X {}}}" =? [find "Y.Z.W"; find "Y.Z.W+X"]
        getTypeSymbols "namespace Y.Z { struct W { enum X {}}}" =? [find "Y.Z.W"; find "Y.Z.W+X"]

    [<Test>]
    let ``finds multiple symbols of different type kind`` () =
        getTypeSymbols "namespace X { class Q {} enum E {} interface I {}} class Z { enum F{} interface I{} }" =?
        [find "X.Q"; find "X.E"; find "X.I";
        find "Z"; find "Z+F"; find "Z+I"]