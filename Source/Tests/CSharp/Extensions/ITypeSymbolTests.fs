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

namespace SafetySharp.Tests.ITypeSymbolTests

open System.Linq
open NUnit.Framework
open FsUnit
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp
open SafetySharp.Tests

[<TestFixture>]
module IsDerivedFromMethod =
    let isDerivedFrom csharpCode baseName =
        let compilation = TestCompilation csharpCode

        let derivedSymbol = compilation.FindTypeSymbol "X"
        let baseSymbol = compilation.FindTypeSymbol baseName

        derivedSymbol.IsDerivedFrom baseSymbol

    [<Test>]
    let ``returns false for self checks`` () =
        isDerivedFrom "interface X {}" "X" |> should be False
        isDerivedFrom "class X {}" "X" |> should be False

    [<Test>]
    let ``returns false when class does not derive from given base class`` () =
        isDerivedFrom "class Q {} class X {}" "Q" |> should be False
        isDerivedFrom "class Q {} class Y {} class X : Y {}" "Q" |> should be False
        isDerivedFrom "class Q {} class Z {} class Y : Z {} class X : Y {}" "Q" |> should be False

    [<Test>]
    let ``returns false when interface does not derive from given base interface`` () =
        isDerivedFrom "interface Q {} interface X {}" "Q" |> should be False
        isDerivedFrom "interface Q {} interface Y {} interface X : Y {}" "Q" |> should be False
        isDerivedFrom "interface Q {} interface Z {} interface Y : Z {} interface X : Y {}" "Q" |> should be False

    [<Test>]
    let ``returns true when class derives from given base class`` () =
        isDerivedFrom "class Y {} class X : Y {}" "Y" |> should be True
        isDerivedFrom "class Z {} class Y : Z {} class X : Y {}" "Y" |> should be True
        isDerivedFrom "class Z {} class Y : Z {} class X : Y {}" "Z" |> should be True

    [<Test>]
    let ``returns true when class has base class that derives from the given base interface`` () =
        isDerivedFrom "interface Q {} interface Z {} class Y : Z, Q {} class X : Y {}" "Q" |> should be True
        isDerivedFrom "interface Q {} interface Z {} class Y : Z, Q {} class X : Y {}" "Z" |> should be True
        isDerivedFrom "interface S {} interface Q {} class Z : Q, S {} class Y : Z, Q {} class X : Y {}" "Q" |> should be True
        isDerivedFrom "interface S {} interface Q {} class Z : Q, S {} class Y : Z, Q {} class X : Y {}" "S" |> should be True

    [<Test>]
    let ``returns true when interface derives from given base interface`` () =
        isDerivedFrom "interface Y {} interface X : Y {}" "Y" |> should be True
        isDerivedFrom "interface Z {} interface Y : Z {} interface X : Y {}" "Y" |> should be True
        isDerivedFrom "interface Z {} interface Y : Z {} interface X : Y {}" "Z" |> should be True
        isDerivedFrom "interface Z {} interface Y : Z {} interface X : Y, Z {}" "Y" |> should be True
        isDerivedFrom "interface Z {} interface Y : Z {} interface X : Y, Z {}" "Z" |> should be True
        isDerivedFrom "interface Z {} interface Y {} interface X : Y, Z {}" "Y" |> should be True
        isDerivedFrom "interface Z {} interface Y {} interface X : Y, Z {}" "Z" |> should be True
        isDerivedFrom "interface Q {} interface Z {} interface Y : Z, Q {} interface X : Y {}" "Q" |> should be True
