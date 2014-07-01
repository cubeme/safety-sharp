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

namespace SafetySharp.Tests.CSharp.Roslyn.MethodDeclarationExtensionsTests

open System
open System.Linq
open NUnit.Framework
open Swensen.Unquote
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Internal.CSharp
open SafetySharp.Tests
open SafetySharp.Modeling
open SafetySharp.Internal.CSharp.Roslyn

[<TestFixture>]
module ``Visibility property`` =

    let private getVisibility csharpCode =
        let compilation = TestCompilation csharpCode
        let methodDeclaration = compilation.FindMethodDeclaration "C" "M"
        methodDeclaration.Visibility

    [<Test>]
    let ``default visibility`` () =
        getVisibility "class C { void M() {}}" =? Private
        getVisibility "interface I { void M(); } class C : I { void I.M() {}}" =? Public

    [<Test>]
    let ``private visibility`` () =
        getVisibility "class C { private void M() {}}" =? Private

    [<Test>]
    let ``protected visibility`` () =
        getVisibility "class C { protected void M() {}}" =? Protected

    [<Test>]
    let ``protected internal visibility`` () =
        getVisibility "class C { protected internal void M() {}}" =? ProtectedInternal
        getVisibility "class C { internal protected void M() {}}" =? ProtectedInternal

    [<Test>]
    let ``internal visibility`` () =
        getVisibility "class C { internal void M() {}}" =? Internal

    [<Test>]
    let ``public visibility`` () =
        getVisibility "class C { public void M() {}}" =? Public