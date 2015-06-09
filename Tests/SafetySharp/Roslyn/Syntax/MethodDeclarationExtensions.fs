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

namespace Roslyn.Syntax.MethodDeclarationExtensions

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Modeling
open SafetySharp.Compiler.Roslyn.Syntax

[<TestFixture>]
module ``GetMethodSymbol method`` =
    let checkMethodSymbol csharpCode typeName methodName =
        let compilation = TestCompilation csharpCode
        let declaration = compilation.FindMethodDeclaration typeName methodName
        let symbol = compilation.FindMethodSymbol typeName methodName

        declaration.GetMethodSymbol compilation.SemanticModel =? symbol
        
    [<Test>]
    let ``throws when method declaration is null`` () =
        let compilation = TestCompilation ""
        raisesArgumentNullException "methodDeclaration" 
            (fun () -> (null : BaseMethodDeclarationSyntax).GetMethodSymbol compilation.SemanticModel |> ignore)

    [<Test>]
    let ``throws when semantic model is null`` () =
        let compilation = TestCompilation "class X { void M() {} }"
        let declaration = compilation.FindMethodDeclaration "X" "M"
        raisesArgumentNullException "semanticModel" (fun () -> declaration.GetMethodSymbol null |> ignore)

    [<Test>]
    let ``returns correct class symbol`` () =
        checkMethodSymbol "class X { void M() {} void N() {} } class Y { void M() {}}" "X" "M"
        checkMethodSymbol "class X { void M() {} void N() {} } class Y { void M() {}}" "X" "N"
        checkMethodSymbol "class X { void M() {} void N() {} } class Y { void M() {}}" "Y" "M"

[<TestFixture>]
module ``Visibility property`` =
    let private getVisibility csharpCode =
        let compilation = TestCompilation csharpCode
        let methodDeclaration = compilation.FindMethodDeclaration "C" "M"
        methodDeclaration.GetVisibility ()

    [<Test>]
    let ``throws if method declaration is null`` () =
        raisesArgumentNullException "methodDeclaration" (fun () -> (null : MethodDeclarationSyntax).GetVisibility() |> ignore)

    [<Test>]
    let ``default visibility`` () =
        getVisibility "class C { void M() {}}" =? Visibility.Private
        getVisibility "interface I { void M(); } class C : I { void I.M() {}}" =? Visibility.Public

    [<Test>]
    let ``private visibility`` () =
        getVisibility "class C { private void M() {}}" =? Visibility.Private

    [<Test>]
    let ``protected visibility`` () =
        getVisibility "class C { protected void M() {}}" =? Visibility.Protected

    [<Test>]
    let ``protected internal visibility`` () =
        getVisibility "class C { protected internal void M() {}}" =? Visibility.ProtectedInternal
        getVisibility "class C { internal protected void M() {}}" =? Visibility.ProtectedInternal

    [<Test>]
    let ``internal visibility`` () =
        getVisibility "class C { internal void M() {}}" =? Visibility.Internal

    [<Test>]
    let ``public visibility`` () =
        getVisibility "class C { public void M() {}}" =? Visibility.Public

[<TestFixture>]
module ``GetDelegateType method`` =

    let getDelegateType csharpCode =
        let compilation = TestCompilation csharpCode
        let methodDeclaration = compilation.FindMethodDeclaration "C" "M"
        methodDeclaration.GetDelegateType compilation.SemanticModel

    [<Test>]
    let ``throws when method declaration is null`` () =
        let compilation = TestCompilation ""
        raisesArgumentNullException "methodDeclaration" 
            (fun () -> (null : MethodDeclarationSyntax).GetDelegateType compilation.SemanticModel |> ignore)

    [<Test>]
    let ``throws when semantic model is null`` () =
        let compilation = TestCompilation "class C { void M() {}}"
        let methodDeclaration = compilation.FindMethodDeclaration "C" "M"
        raisesArgumentNullException "semanticModel" (fun () -> methodDeclaration.GetDelegateType null |> ignore)

    [<Test>]
    let ``returns Action for void-returning parameterless method`` () =
        getDelegateType "class C { void M() {}}" =? "System.Action"

    [<Test>]
    let ``returns Action<> for void-returning method with parameters`` () =
        getDelegateType "class C { void M(int i) {}}" =? "System.Action<int>"
        getDelegateType "class C { void M(int i, System.Boolean b, object o) {}}" =? "System.Action<int, System.Boolean, object>"
        getDelegateType "class C { void M(int i, int? x) {}}" =? "System.Action<int, int?>"

    [<Test>]
    let ``returns Func<> for non-void-returning method without parameters`` () =
        getDelegateType "class C { int M() { return 0; }}" =? "System.Func<int>"
        getDelegateType "class C { System.Boolean? M() { return null; }}" =? "System.Func<System.Boolean?>"

    [<Test>]
    let ``returns Func<> for non-void-returning method with parameters`` () =
        getDelegateType "class C { int M(int i) { return 0; }}" =? "System.Func<int, int>"
        getDelegateType "class C { int? M(int i, System.Boolean b, object o) { return null; }}" =? "System.Func<int, System.Boolean, object, int?>"
        getDelegateType "class C { int M(int i, int? x) { return 0; }}" =? "System.Func<int, int?, int>"