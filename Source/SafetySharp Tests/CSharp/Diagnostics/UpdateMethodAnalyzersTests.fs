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

namespace SafetySharp.Tests.CSharp.Diagnostics.UpdateMethodAnalyzersTests

open System.Linq
open System.Threading
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Diagnostics
open SafetySharp.Internal.CSharp
open SafetySharp.Tests
open SafetySharp.Internal.CSharp.Diagnostics
open SafetySharp.Internal.CSharp.Roslyn

[<TestFixture>]
module UpdateMethodReturnTypeAnalyzerTests =
    let hasDiagnostics = TestCompilation.HasDiagnostics (UpdateMethodReturnTypeAnalyzer ())

    [<Test>]
    let ``Void returning update method should be valid`` () =
        hasDiagnostics "class C : Component { [Behavior] void M() {}}" =? false

    [<Test>]
    let ``Non-void returning update method should be invalid`` () =
        hasDiagnostics "class C : Component { [Behavior] int M() { return 0; }}" =? true

    [<Test>]
    let ``Non-void returning update method outside of any component should be valid`` () =
        hasDiagnostics "class C { [Behavior] int M() { return 0; }}" =? false

[<TestFixture>]
module UpdateMethodParameterAnalyzerTests =
    let hasDiagnostics = TestCompilation.HasDiagnostics (UpdateMethodParameterAnalyzer ())

    [<Test>]
    let ``Parameterless update method should be valid`` () =
        hasDiagnostics "class C : Component { [Behavior] void M() {}}" =? false

    [<Test>]
    let ``Update method with parameters should be invalid`` () =
        hasDiagnostics "class C : Component { [Behavior] void M(int a) {}}" =? true
        hasDiagnostics "class C : Component { [Behavior] void M(int a, bool b) {}}" =? true

    [<Test>]
    let ``Update method with parameters outside of any component should be valid`` () =
        hasDiagnostics "class C { [Behavior] void M(int a) {}}" =? false

[<TestFixture>]
module MultipleUpdateMethodsAnalyzerTests =
    let hasDiagnostics = TestCompilation.HasDiagnostics (MultipleUpdateMethodsAnalyzer ())

    [<Test>]
    let ``Single update method should be valid`` () =
        hasDiagnostics "class C : Component { [Behavior] void M() {}}" =? false

    [<Test>]
    let ``Multiple update methods should be invalid`` () =
        hasDiagnostics "class C : Component { [Behavior] void M() {} [Behavior] void N() {}}" =? true
        hasDiagnostics "class C : Component { [Behavior] void M() {} [Behavior] void N() {} [Behavior] void O() {}}" =? true

    [<Test>]
    let ``Multiple update methods outside of any component should be valid`` () =
        hasDiagnostics "class C { [Behavior] void M() {} [Behavior] void N() {}}" =? false

[<TestFixture>]
module UpdateMethodWithoutBodyAnalyzer =
    let hasDiagnostics = TestCompilation.HasDiagnostics (UpdateMethodWithoutBodyAnalyzer ())

    [<Test>]
    let ``Update method with body should be valid`` () =
        hasDiagnostics "class C : Component { [Behavior] void M() {}}" =? false

    [<Test>]
    let ``Update method without body should be invalid`` () =
        hasDiagnostics "abstract class C : Component { [Behavior] public abstract void M(); }" =? true
        hasDiagnostics "class C : Component { [Behavior] extern void M(); }" =? true

    [<Test>]
    let ``Update method without body outside of any component should be valid`` () =
        hasDiagnostics "class C { [Behavior] extern void M(); }" =? false