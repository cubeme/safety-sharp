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

namespace SafetySharp.Tests.CSharp.Normalization

open System.Linq
open System.Threading
open NUnit.Framework
open Swensen.Unquote
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Diagnostics
open SafetySharp.Internal.CSharp
open SafetySharp.Tests
open SafetySharp.Internal.CSharp.Normalization
open SafetySharp.Internal.CSharp.Roslyn

[<TestFixture>]
module UpdateMethodVisibilityNormalizerTests =

    let private normalize csharpCode =
        let compilation = TestCompilation (csharpCode, SafetySharpAssembly.Modeling)
        let syntaxTree = UpdateMethodVisibilityNormalizer().Normalize(compilation.CSharpCompilation).SyntaxTrees.Single ()
        syntaxTree.Descendants<MethodDeclarationSyntax>().Last().Visibility
    
    [<Test>]
    let ``changes visibility of Update method of non-inherited component`` () =
        normalize "class C : Component { protected override void Update() {} }" =? Public

    [<Test>]
    let ``changes visibility of Update method of inherited component`` () =
        normalize "class D : Component {} class C : D { protected override void Update() {} }" =? Public
        normalize "class D : Component { protected override void Update() {} } class C : D { protected override void Update() {} }" =? Public

    [<Test>]
    let ``does not change visibility of non-Update method`` () =
        normalize "class C : Component { private void M () {} }" =? Private
        normalize "class C : Component { protected void M () {} }" =? Protected
        normalize "class C : Component { protected internal virtual void M () {} }" =? ProtectedInternal
        normalize "class C : Component { internal protected void M () {} }" =? ProtectedInternal
        normalize "class C : Component { internal void M () {} }" =? Internal
        normalize "abstract class C : Component { public abstract void M (); }" =? Public

    [<Test>]
    let ``does not change visibility of non-component Update method`` () =
        normalize "class Base { protected virtual void Update() {} } class C : Base { protected override void Update() {} }" =? Protected

    [<Test>]
    let ``preserves all line breaks in method declaration`` () =
        let csharpCode = "class C : Component { \nprotected\n \noverride void \nUpdate(\n) { \nvar i = 0; ++i; \n} }"
        let compilation = TestCompilation (csharpCode, SafetySharpAssembly.Modeling)
        let syntaxTree = UpdateMethodVisibilityNormalizer().Normalize(compilation.CSharpCompilation).SyntaxTrees.Single ()
        let classDeclaration = syntaxTree.Descendants<ClassDeclarationSyntax>().Single ()

        let actual = classDeclaration.ToFullString ()
        let expected = "class C : Component { \npublic\n \noverride void \nUpdate(\n) { \nvar i = 0; ++i; \n} }"

        actual =? expected