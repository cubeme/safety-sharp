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

namespace SafetySharp.Tests.CSharp.Diagnostics.PortAnalyzersTests

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
module MarkedWithBothProvidedAndRequiredAttributesAnalyzerTests =
    let hasDiagnostics = TestCompilation.HasDiagnostics (MarkedWithBothProvidedAndRequiredAttributesAnalyzer ())

    [<Test>]
    let ``Method or property without attributes is valid`` () =
        hasDiagnostics "class C : Component { void M() {}}" =? false
        hasDiagnostics "class C : Component { int M { get; set; }}" =? false

    [<Test>]
    let ``Method or property without only one of the attributes is valid`` () =
        hasDiagnostics "class C : Component { [Required] void M() {}}" =? false
        hasDiagnostics "class C : Component { [Required] int M { get; set; }}" =? false
        hasDiagnostics "class C : Component { [Provided] void M() {}}" =? false
        hasDiagnostics "class C : Component { [Provided] int M { get; set; }}" =? false

    [<Test>]
    let ``Method or property with both attributes is invalid`` () =
        hasDiagnostics "class C : Component { [Required, Provided] void M() {}}" =? true
        hasDiagnostics "class C : Component { [Required, Provided] int M { get; set; }}" =? true
        hasDiagnostics "class C : Component { [Required] [Provided] void M() {}}" =? true
        hasDiagnostics "class C : Component { [Required] [Provided] int M { get; set; }}" =? true

    [<Test>]
    let ``Method or property with both attributes outside of component class is valid`` () =
        hasDiagnostics "class C { [Required, Provided] void M() {}}" =? false
        hasDiagnostics "class C { [Required, Provided] int M { get; set; }}" =? false
        hasDiagnostics "class C { [Required] [Provided] void M() {}}" =? false
        hasDiagnostics "class C { [Required] [Provided] int M { get; set; }}" =? false

[<TestFixture>]
module ExternProvidedPortAnalyzerTests =
    let hasDiagnostics = TestCompilation.HasDiagnostics (ExternProvidedPortAnalyzer ())

    [<Test>]
    let ``Method or property without attributes is valid`` () =
        hasDiagnostics "class C : Component { void M() {}}" =? false
        hasDiagnostics "class C : Component { int M { get; set; }}" =? false
        hasDiagnostics "class C : Component { extern void M(); }" =? false
        hasDiagnostics "class C : Component { extern int M { get; set; }}" =? false

    [<Test>]
    let ``Non-extern method or property with Provided attribute is valid`` () =
        hasDiagnostics "class C : Component { [Provided] void M() {}}" =? false
        hasDiagnostics "class C : Component { [Provided] int M { get; set; }}" =? false

    [<Test>]
    let ``Extern method or property with Provided attribute is invalid`` () =
        hasDiagnostics "class C : Component { [Provided] extern void M();}" =? true
        hasDiagnostics "class C : Component { [Provided] extern int M { get; set; }}" =? true

    [<Test>]
    let ``Extern method or property with Provided attribute outside of component classes is valid`` () =
        hasDiagnostics "class C { [Provided] extern void M();}" =? false
        hasDiagnostics "class C { [Provided] extern int M { get; set; }}" =? false

[<TestFixture>]
module NonExternRequiredPortAnalyzerTests =
    let hasDiagnostics = TestCompilation.HasDiagnostics (NonExternRequiredPortAnalyzer ())

    [<Test>]
    let ``Method or property without attributes is valid`` () =
        hasDiagnostics "class C : Component { void M() {}}" =? false
        hasDiagnostics "class C : Component { int M { get; set; }}" =? false
        hasDiagnostics "class C : Component { extern void M(); }" =? false
        hasDiagnostics "class C : Component { extern int M { get; set; }}" =? false

    [<Test>]
    let ``Non-extern method or property with Required attribute is invalid`` () =
        hasDiagnostics "class C : Component { [Required] void M() {}}" =? true
        hasDiagnostics "class C : Component { [Required] int M { get; set; }}" =? true

    [<Test>]
    let ``Extern method or property with Required attribute is valid`` () =
        hasDiagnostics "class C : Component { [Required] extern void M();}" =? false
        hasDiagnostics "class C : Component { [Required] extern int M { get; set; }}" =? false

    [<Test>]
    let ``Non-extern method or property with Required attribute outside of component classes is valid`` () =
        hasDiagnostics "class C { [Provided] void M() {}}" =? false
        hasDiagnostics "class C { [Provided] int M { get; set; }}" =? false
