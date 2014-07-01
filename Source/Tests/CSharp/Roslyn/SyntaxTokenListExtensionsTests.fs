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

namespace SafetySharp.Tests.CSharp.Roslyn.SyntaxTokenListExtensionsTests

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Internal.CSharp
open SafetySharp.Tests
open SafetySharp.Modeling
open SafetySharp.Internal.CSharp.Roslyn

[<TestFixture>]
module ``Visibility method`` =
    
    let private getVisibility csharpModifiers =
        let compilation = TestCompilation ("
            class C {
                " + csharpModifiers + " void M() { }
            }
        ")

        let methodDeclaration = compilation.FindMethodDeclaration "C" "M"
        methodDeclaration.Modifiers.GetVisibility Private

    [<Test>]
    let ``default visibility`` () =
        getVisibility "" =? Private

    [<Test>]
    let ``private visibility`` () =
        getVisibility "private" =? Private

    [<Test>]
    let ``protected visibility`` () =
        getVisibility "protected" =? Protected

    [<Test>]
    let ``protected internal visibility`` () =
        getVisibility "protected internal" =? ProtectedInternal
        getVisibility "internal protected" =? ProtectedInternal

    [<Test>]
    let ``internal visibility`` () =
        getVisibility "internal" =? Internal

    [<Test>]
    let ``public visibility`` () =
        getVisibility "public" =? Public