// The MIT License (MIT)
// open SafetySharp.Modeling
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

namespace Roslyn.Syntax.BaseTypeDeclarationExtensions

open System
open System.Linq
open System.Runtime.CompilerServices
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Modeling.CompilerServices
open SafetySharp.CSharp.Roslyn.Syntax
open SafetySharp.CSharp.Roslyn.Symbols

[<TestFixture>]
module ``GetTypeSymbol method`` =
    let checkTypeSymbol csharpCode typeName =
        let compilation = TestCompilation csharpCode
        let declaration = compilation.FindTypeDeclaration typeName
        let symbol = compilation.FindTypeSymbol typeName

        declaration.GetTypeSymbol compilation.SemanticModel =? symbol

    [<Test>]
    let ``throws when type declaration is null`` () =
        let compilation = TestCompilation ""
        raisesArgumentNullException "typeDeclaration" (fun () -> (null : BaseTypeDeclarationSyntax).GetTypeSymbol compilation.SemanticModel |> ignore)

    [<Test>]
    let ``throws when semantic model is null`` () =
        let compilation = TestCompilation "class X {}"
        let declaration = compilation.FindClassDeclaration "X"
        raisesArgumentNullException "semanticModel" (fun () -> declaration.GetTypeSymbol null |> ignore)

    [<Test>]
    let ``returns correct class symbol`` () =
        checkTypeSymbol "class X {} class Y {}" "X"
        checkTypeSymbol "class X {} class Y {}" "Y"

    [<Test>]
    let ``returns correct interface symbol`` () =
        checkTypeSymbol "interface X {} class Y {}" "X"
        checkTypeSymbol "class X {} interface Y {}" "Y"
        checkTypeSymbol "interface X {} interface Y {}" "Y"

    [<Test>]
    let ``returns correct enum symbol`` () =
        checkTypeSymbol "enum X {} class Y {}" "X"
        checkTypeSymbol "class X {} enum Y {}" "Y"
        checkTypeSymbol "enum X {} enum Y {}" "Y"

    [<Test>]
    let ``returns correct struct symbol`` () =
        checkTypeSymbol "struct X {} class Y {}" "X"
        checkTypeSymbol "class X {} struct Y {}" "Y"
        checkTypeSymbol "struct X {} struct Y {}" "Y"

[<TestFixture>]
module ``IsDerivedFrom method`` =
    let isDerivedFrom csharpCode baseName =
        let compilation = TestCompilation csharpCode

        let derivedDeclaration = compilation.FindTypeDeclaration "X"
        let baseDeclaration = compilation.FindTypeSymbol baseName

        derivedDeclaration.IsDerivedFrom (compilation.SemanticModel, baseDeclaration)

    [<Test>]
    let ``throws when type declaration is null`` () =
        let compilation = TestCompilation "class X {}"
        let symbol = compilation.FindClassSymbol "X"
        raisesArgumentNullException "typeDeclaration" 
            (fun () -> (null : BaseTypeDeclarationSyntax).IsDerivedFrom (compilation.SemanticModel, symbol) |> ignore)

    [<Test>]
    let ``throws when semantic model is null`` () =
        let compilation = TestCompilation "class X {}"
        let declaration = compilation.FindClassDeclaration "X"
        let symbol = compilation.FindClassSymbol "X"
        raisesArgumentNullException "semanticModel" (fun () -> declaration.IsDerivedFrom (null, symbol) |> ignore)

    [<Test>]
    let ``throws when base type symbol is null`` () =
        let compilation = TestCompilation "class X {}"
        let declaration = compilation.FindClassDeclaration "X"
        raisesArgumentNullException "baseType" (fun () -> declaration.IsDerivedFrom (compilation.SemanticModel, null) |> ignore)

    [<Test>]
    let ``throws when base type is null`` () =
        let compilation = TestCompilation ""
        let symbol = compilation.CSharpCompilation.GetTypeSymbol<obj> ()
        raisesArgumentNullException "baseType" (fun () -> symbol.IsDerivedFrom null |> ignore)

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
module ``IsDerivedFromComponent methods`` =
    let isDerivedFromComponent csharpCode =
        let compilation = TestCompilation csharpCode
        let derivedDeclaration = compilation.FindTypeDeclaration "X"

        derivedDeclaration.IsDerivedFromComponent compilation.SemanticModel

    [<Test>]
    let ``throws when type declaration is null`` () =
        let compilation = TestCompilation("class X {}")
        raisesArgumentNullException "typeDeclaration" (fun () -> (null : BaseTypeDeclarationSyntax).IsDerivedFromComponent compilation.SemanticModel |> ignore)

    [<Test>]
    let ``throws when semantic model is null`` () =
        let declaration = TestCompilation("class X {}").FindClassDeclaration "X"
        raisesArgumentNullException "semanticModel" (fun () -> declaration.IsDerivedFromComponent (null : SemanticModel) |> ignore)

    [<Test>]
    let ``returns false for class with no base`` () =
        isDerivedFromComponent "class X {}" =? false

    [<Test>]
    let ``returns false for class with non-Component base`` () =
        isDerivedFromComponent "class Y { } class X : Y {}" =? false

    [<Test>]
    let ``returns false for class only implementing IComponent`` () =
        isDerivedFromComponent "class X : IComponent { public void Update() {} }" =? false

    [<Test>]
    let ``returns true for class directly derived from Component`` () =
        isDerivedFromComponent "class X : Component {}" =? true

    [<Test>]
    let ``returns true for class indirectly derived from Component`` () =
        isDerivedFromComponent "class Y : Component {} class X : Y {}" =? true

[<TestFixture>]
module ``ImplementsIComponent methods`` =
    let implementsIComponent csharpCode =
        let compilation = TestCompilation csharpCode
        let derivedDeclaration = compilation.FindTypeDeclaration "X"

        derivedDeclaration.ImplementsIComponent compilation.SemanticModel

    [<Test>]
    let ``throws when type declaration is null`` () =
        let compilation = TestCompilation("class X {}")
        raisesArgumentNullException "typeDeclaration" (fun () -> (null : BaseTypeDeclarationSyntax).ImplementsIComponent compilation.SemanticModel |> ignore)

    [<Test>]
    let ``throws when semantic model is null`` () =
        let symbol = TestCompilation("class X {}").FindTypeSymbol("X")
        raisesArgumentNullException "semanticModel" (fun () -> symbol.ImplementsIComponent (null : SemanticModel) |> ignore)

    [<Test>]
    let ``returns false for class with no base`` () =
        implementsIComponent "class X {}" =? false

    [<Test>]
    let ``returns false for class with non-Component base`` () =
        implementsIComponent "class Y { } class X : Y {}" =? false

    [<Test>]
    let ``returns true for class only implementing IComponent`` () =
        implementsIComponent "class X : IComponent { public void Update() {} }" =? true

    [<Test>]
    let ``returns true for class directly derived from Component`` () =
        implementsIComponent "class X : Component {}" =? true

    [<Test>]
    let ``returns true for class indirectly derived from Component`` () =
        implementsIComponent "class Y : Component {} class X : Y {}" =? true

    [<Test>]
    let ``returns true for class indirectly implementing IComponent`` () =
        implementsIComponent "class Y : IComponent { public void Update() {} } class X : Y {}" =? true