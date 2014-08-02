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

namespace SafetySharp.CSharpCompiler.Tests.Roslyn.Syntax.MethodDeclarationExtensionsTests

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Internal.CSharp
open SafetySharp.Modeling
open SafetySharp.CSharpCompiler.Roslyn.Syntax

//[<TestFixture>]
//module ``Visibility property`` =
//
//    let private getVisibility csharpCode =
//        let compilation = TestCompilation csharpCode
//        let methodDeclaration = compilation.FindMethodDeclaration "C" "M"
//        methodDeclaration.Visibility
//
//    [<Test>]
//    let ``default visibility`` () =
//        getVisibility "class C { void M() {}}" =? Private
//        getVisibility "interface I { void M(); } class C : I { void I.M() {}}" =? Public
//
//    [<Test>]
//    let ``private visibility`` () =
//        getVisibility "class C { private void M() {}}" =? Private
//
//    [<Test>]
//    let ``protected visibility`` () =
//        getVisibility "class C { protected void M() {}}" =? Protected
//
//    [<Test>]
//    let ``protected internal visibility`` () =
//        getVisibility "class C { protected internal void M() {}}" =? ProtectedInternal
//        getVisibility "class C { internal protected void M() {}}" =? ProtectedInternal
//
//    [<Test>]
//    let ``internal visibility`` () =
//        getVisibility "class C { internal void M() {}}" =? Internal
//
//    [<Test>]
//    let ``public visibility`` () =
//        getVisibility "class C { public void M() {}}" =? Public
//
//[<TestFixture>]
//module ``GetDelegateType method`` =
//
//    let getDelegateType csharpCode =
//        let compilation = TestCompilation csharpCode
//        let methodDeclaration = compilation.FindMethodDeclaration "C" "M"
//        methodDeclaration.GetDelegateType compilation.SemanticModel
//
//    [<Test>]
//    let ``throws when semantic model is null`` () =
//        let compilation = TestCompilation "class C { void M() {}}"
//        let methodDeclaration = compilation.FindMethodDeclaration "C" "M"
//        raisesArgumentNullException "semanticModel" (fun () -> methodDeclaration.GetDelegateType null |> ignore)
//
//    [<Test>]
//    let ``returns Action for void-returning parameterless method`` () =
//        getDelegateType "class C { void M() {}}" =? "System.Action"
//
//    [<Test>]
//    let ``returns Action<> for void-returning method with parameters`` () =
//        getDelegateType "class C { void M(int i) {}}" =? "System.Action<int>"
//        getDelegateType "class C { void M(int i, System.Boolean b, object o) {}}" =? "System.Action<int, System.Boolean, object>"
//        getDelegateType "class C { void M(int i, int? x) {}}" =? "System.Action<int, int?>"
//
//    [<Test>]
//    let ``returns Func<> for non-void-returning method without parameters`` () =
//        getDelegateType "class C { int M() { return 0; }}" =? "System.Func<int>"
//        getDelegateType "class C { System.Boolean? M() { return null; }}" =? "System.Func<System.Boolean?>"
//
//    [<Test>]
//    let ``returns Func<> for non-void-returning method with parameters`` () =
//        getDelegateType "class C { int M(int i) { return 0; }}" =? "System.Func<int, int>"
//        getDelegateType "class C { int? M(int i, System.Boolean b, object o) { return null; }}" =? "System.Func<int, System.Boolean, object, int?>"
//        getDelegateType "class C { int M(int i, int? x) { return 0; }}" =? "System.Func<int, int?, int>"
//
//[<TestFixture>]
//module ``HasAttribute method`` =
//    let hasAttribute<'T when 'T :> Attribute> csharpCode =
//        let compilation = TestCompilation csharpCode
//        let methodDeclaration = compilation.FindMethodDeclaration "C" "M"
//        methodDeclaration.HasAttribute<'T> compilation.SemanticModel
//
//    [<Test>]
//    let ``throws when compilation is null`` () =
//        let compilation = TestCompilation "class C { void M() {}}"
//        let methodSymbol = compilation.FindMethodSymbol "C" "M"
//        raisesArgumentNullException "compilation" (fun () -> methodSymbol.HasAttribute<ProvidedAttribute> null |> ignore)
//
//    [<Test>]
//    let ``returns false if method has no attribute`` () =
//        hasAttribute<ProvidedAttribute> "class C { void M() {}}" =? false
//
//    [<Test>]
//    let ``returns false if method has different attribute`` () =
//        hasAttribute<ProvidedAttribute> "class C { [Required] void M() {}}" =? false
//
//    [<Test>]
//    let ``returns true if method has attribute`` () =
//        hasAttribute<ProvidedAttribute> "class C { [Provided] void M() {}}" =? true