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

namespace SafetySharp.Tests.CSharp.Roslyn.ITypeSymbolExtensionsTests

open System.Linq
open NUnit.Framework
open Swensen.Unquote
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp
open SafetySharp.Tests
open SafetySharp.CSharp.Roslyn

[<TestFixture>]
module ``IsDerivedFrom method`` =
    let isDerivedFrom csharpCode baseName =
        let compilation = TestCompilation csharpCode

        let derivedSymbol = compilation.FindTypeSymbol "X"
        let baseSymbol = compilation.FindTypeSymbol baseName

        derivedSymbol.IsDerivedFrom baseSymbol

    [<Test>]
    let ``returns false for self checks`` () =
        isDerivedFrom "interface X {}" "X" =? false
        isDerivedFrom "class X {}" "X" =? false

    [<Test>]
    let ``returns false when class does not derive from given base class`` () =
        isDerivedFrom "class Q {} class X {}" "Q" =? false
        isDerivedFrom "class Q {} class Y {} class X : Y {}" "Q" =? false
        isDerivedFrom "class Q {} class Z {} class Y : Z {} class X : Y {}" "Q" =? false

    [<Test>]
    let ``returns false when interface does not derive from given base interface`` () =
        isDerivedFrom "interface Q {} interface X {}" "Q" =? false
        isDerivedFrom "interface Q {} interface Y {} interface X : Y {}" "Q" =? false
        isDerivedFrom "interface Q {} interface Z {} interface Y : Z {} interface X : Y {}" "Q" =? false

    [<Test>]
    let ``returns true when class derives from given base class`` () =
        isDerivedFrom "class Y {} class X : Y {}" "Y" =? true
        isDerivedFrom "class Z {} class Y : Z {} class X : Y {}" "Y" =? true
        isDerivedFrom "class Z {} class Y : Z {} class X : Y {}" "Z" =? true

    [<Test>]
    let ``returns true when class has base class that derives from the given base interface`` () =
        isDerivedFrom "interface Q {} interface Z {} class Y : Z, Q {} class X : Y {}" "Q" =? true
        isDerivedFrom "interface Q {} interface Z {} class Y : Z, Q {} class X : Y {}" "Z" =? true
        isDerivedFrom "interface S {} interface Q {} class Z : Q, S {} class Y : Z, Q {} class X : Y {}" "Q" =? true
        isDerivedFrom "interface S {} interface Q {} class Z : Q, S {} class Y : Z, Q {} class X : Y {}" "S" =? true

    [<Test>]
    let ``returns true when interface derives from given base interface`` () =
        isDerivedFrom "interface Y {} interface X : Y {}" "Y" =? true
        isDerivedFrom "interface Z {} interface Y : Z {} interface X : Y {}" "Y" =? true
        isDerivedFrom "interface Z {} interface Y : Z {} interface X : Y {}" "Z" =? true
        isDerivedFrom "interface Z {} interface Y : Z {} interface X : Y, Z {}" "Y" =? true
        isDerivedFrom "interface Z {} interface Y : Z {} interface X : Y, Z {}" "Z" =? true
        isDerivedFrom "interface Z {} interface Y {} interface X : Y, Z {}" "Y" =? true
        isDerivedFrom "interface Z {} interface Y {} interface X : Y, Z {}" "Z" =? true
        isDerivedFrom "interface Q {} interface Z {} interface Y : Z, Q {} interface X : Y {}" "Q" =? true

[<TestFixture>]
module ``IsDerivedFromComponent method`` =
    let isDerivedFromComponent csharpCode =
        let compilation = TestCompilation csharpCode
        let derivedSymbol = compilation.FindTypeSymbol "X"

        derivedSymbol.IsDerivedFromComponent compilation.SemanticModel

    [<Test>]
    let ``throws when semantic model is null`` () =
        let symbol = TestCompilation("class X {}").FindTypeSymbol("X")
        raisesArgumentNullException "semanticModel" <@ symbol.IsDerivedFromComponent (null : SemanticModel) @>

    [<Test>]
    let ``returns false for class with no base`` () =
        isDerivedFromComponent "class X {}" =? false

    [<Test>]
    let ``returns false for class with non-Component base`` () =
        isDerivedFromComponent "class Y { } class X : Y {}" =? false

    [<Test>]
    let ``returns false for class only implementing IComponent`` () =
        isDerivedFromComponent "class X : IComponent { public string Name {get;private set;} }" =? false

    [<Test>]
    let ``returns true for class directly derived from Component`` () =
        isDerivedFromComponent "class X : Component {}" =? true

    [<Test>]
    let ``returns true for class indirectly derived from Component`` () =
        isDerivedFromComponent "class Y : Component {} class X : Y {}" =? true

[<TestFixture>]
module ``ImplementsIComponent method`` =
    let implementsIComponent csharpCode =
        let compilation = TestCompilation csharpCode
        let derivedSymbol = compilation.FindTypeSymbol "X"

        derivedSymbol.ImplementsIComponent compilation.SemanticModel

    [<Test>]
    let ``throws when semantic model is null`` () =
        let symbol = TestCompilation("class X {}").FindTypeSymbol("X")
        raisesArgumentNullException "semanticModel" <@ symbol.ImplementsIComponent (null : SemanticModel) @>

    [<Test>]
    let ``returns false for class with no base`` () =
        implementsIComponent "class X {}" =? false

    [<Test>]
    let ``returns false for class with non-Component base`` () =
        implementsIComponent "class Y { } class X : Y {}" =? false

    [<Test>]
    let ``returns true for class only implementing IComponent`` () =
        implementsIComponent "class X : IComponent { public string Name {get;private set;} }" =? true

    [<Test>]
    let ``returns true for class directly derived from Component`` () =
        implementsIComponent "class X : Component {}" =? true

    [<Test>]
    let ``returns true for class indirectly derived from Component`` () =
        implementsIComponent "class Y : Component {} class X : Y {}" =? true

    [<Test>]
    let ``returns true for class indirectly implementing IComponent`` () =
        implementsIComponent "class Y : IComponent { public string Name {get;private set;} } class X : Y {}" =? true