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
        hasDiagnostics "interface C : IComponent { void M(); }" =? false
        hasDiagnostics "interface C : IComponent { int M { get; set; }}" =? false

    [<Test>]
    let ``Method or property with only one of the attributes is valid`` () =
        hasDiagnostics "class C : Component { [Required] void M() {}}" =? false
        hasDiagnostics "class C : Component { [Required] int M { get; set; }}" =? false
        hasDiagnostics "class C : Component { [Provided] void M() {}}" =? false
        hasDiagnostics "class C : Component { [Provided] int M { get; set; }}" =? false
        hasDiagnostics "interface C : IComponent { [Required] void M(); }" =? false
        hasDiagnostics "interface C : IComponent { [Required] int M { get; set; }}" =? false
        hasDiagnostics "interface C : IComponent { [Provided] void M(); }" =? false
        hasDiagnostics "interface C : IComponent { [Provided] int M { get; set; }}" =? false

    [<Test>]
    let ``Method or property with both attributes is invalid`` () =
        hasDiagnostics "class C : Component { [Required, Provided] void M() {}}" =? true
        hasDiagnostics "class C : Component { [Required, Provided] int M { get; set; }}" =? true
        hasDiagnostics "class C : Component { [Required] [Provided] void M() {}}" =? true
        hasDiagnostics "class C : Component { [Required] [Provided] int M { get; set; }}" =? true
        hasDiagnostics "interface C : IComponent { [Required, Provided] void M(); }" =? true
        hasDiagnostics "interface C : IComponent { [Required, Provided] int M { get; set; }}" =? true
        hasDiagnostics "interface C : IComponent { [Required] [Provided] void M(); }" =? true
        hasDiagnostics "interface C : IComponent { [Required] [Provided] int M { get; set; }}" =? true

    [<Test>]
    let ``Method or property with both attributes outside of component class or interface is valid`` () =
        hasDiagnostics "class C { [Required, Provided] void M() {}}" =? false
        hasDiagnostics "class C { [Required, Provided] int M { get; set; }}" =? false
        hasDiagnostics "class C { [Required] [Provided] void M() {}}" =? false
        hasDiagnostics "class C { [Required] [Provided] int M { get; set; }}" =? false
        hasDiagnostics "interface C { [Required, Provided] void M(); }" =? false
        hasDiagnostics "interface C { [Required, Provided] int M { get; set; }}" =? false
        hasDiagnostics "interface C { [Required] [Provided] void M(); }" =? false
        hasDiagnostics "interface C { [Required] [Provided] int M { get; set; }}" =? false

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

[<TestFixture>]
module ComponentInterfaceMethodWithoutPortAttributeAnalyzerTests =
    let hasDiagnostics = TestCompilation.HasDiagnostics (ComponentInterfaceMethodWithoutPortAttributeAnalyzer ())

    [<Test>]
    let ``Method or property without attributes is invalid`` () =
        hasDiagnostics "interface C : IComponent { void M(); }" =? true
        hasDiagnostics "interface C : IComponent { int M { get; set; }}" =? true

    [<Test>]
    let ``Method or property with only one of the attributes is valid`` () =
        hasDiagnostics "interface C : IComponent { [Required] void M(); }" =? false
        hasDiagnostics "interface C : IComponent { [Required] int M { get; set; }}" =? false
        hasDiagnostics "interface C : IComponent { [Provided] void M(); }" =? false
        hasDiagnostics "interface C : IComponent { [Provided] int M { get; set; }}" =? false

    [<Test>]
    let ``Method or property with both attributes is valid`` () =
        hasDiagnostics "interface C : IComponent { [Required, Provided] void M(); }" =? false
        hasDiagnostics "interface C : IComponent { [Required, Provided] int M { get; set; }}" =? false
        hasDiagnostics "interface C : IComponent { [Required] [Provided] void M(); }" =? false
        hasDiagnostics "interface C : IComponent { [Required] [Provided] int M { get; set; }}" =? false

    [<Test>]
    let ``Method or property without attributes outside of component interface is valid`` () =
        hasDiagnostics "interface C { void M(); }" =? false
        hasDiagnostics "interface C { int M { get; set; }}" =? false
        hasDiagnostics "class C : Component { void M() {} }" =? false
        hasDiagnostics "class C : Component { int M { get; set; }}" =? false
        hasDiagnostics "class C { void M() {} }" =? false
        hasDiagnostics "class C { int M { get; set; }}" =? false
        hasDiagnostics "class C : IComponent { void M() {} }" =? false
        hasDiagnostics "class C : IComponent { int M { get; set; }}" =? false

[<TestFixture>]
module AccessorIsMarkedWithPortAttributeAnalyzerTests =
    let hasDiagnostics = TestCompilation.HasDiagnostics (AccessorIsMarkedWithPortAttributeAnalyzer ())

    [<Test>]
    let ``Accessors without attributes are valid`` () =
        hasDiagnostics "class C : Component { int M { get; set; }}" =? false
        hasDiagnostics "interface C : IComponent { int M { get; set; }}" =? false

    [<Test>]
    let ``Accessors with single attribute are invalid`` () =
        hasDiagnostics "class C : Component { int M { [Required] get; set; }}" =? true
        hasDiagnostics "class C : Component { int M { [Provided] get; set; }}" =? true
        hasDiagnostics "class C : Component { int M { get; [Required] set; }}" =? true
        hasDiagnostics "class C : Component { int M { get; [Provided] set; }}" =? true
        hasDiagnostics "class C : Component { int M { [Required] get; [Required] set; }}" =? true
        hasDiagnostics "class C : Component { int M { [Provided] get; [Provided] set; }}" =? true
        hasDiagnostics "interface C : IComponent { int M { [Required] get; set; }}" =? true
        hasDiagnostics "interface C : IComponent { int M { [Provided] get; set; }}" =? true
        hasDiagnostics "interface C : IComponent { int M { get; [Required] set; }}" =? true
        hasDiagnostics "interface C : IComponent { int M { get; [Provided] set; }}" =? true
        hasDiagnostics "interface C : IComponent { int M { [Required] get; [Required] set; }}" =? true
        hasDiagnostics "interface C : IComponent { int M { [Provided] get; [Provided] set; }}" =? true

    [<Test>]
    let ``Accessors with both attributes are invalid`` () =
        hasDiagnostics "class C : Component { int M { [Required, Provided] get; set; }}" =? true
        hasDiagnostics "class C : Component { int M { get; [Required, Provided] set; }}" =? true
        hasDiagnostics "class C : Component { int M { [Required, Provided] get; [Required, Provided] set; }}" =? true
        hasDiagnostics "class C : Component { int M { [Required] [Provided] get; set; }}" =? true
        hasDiagnostics "class C : Component { int M { get; [Required] [Provided] set; }}" =? true
        hasDiagnostics "class C : Component { int M { [Required] [Provided] get; [Required] [Provided] set; }}" =? true
        hasDiagnostics "interface C : IComponent { int M { [Required, Provided] get; set; }}" =? true
        hasDiagnostics "interface C : IComponent { int M { get; [Required, Provided] set; }}" =? true
        hasDiagnostics "interface C : IComponent { int M { [Required, Provided] get; [Required, Provided] set; }}" =? true
        hasDiagnostics "interface C : IComponent { int M { [Required] [Provided] get; set; }}" =? true
        hasDiagnostics "interface C : IComponent { int M { get; [Required] [Provided] set; }}" =? true
        hasDiagnostics "interface C : IComponent { int M { [Required] [Provided] get; [Required] [Provided] set; }}" =? true

    [<Test>]
    let ``Accessors with attributes outside of component class or interface are valid`` () =
        hasDiagnostics "class C { int M { [Required, Provided] get; set; }}" =? false
        hasDiagnostics "class C { int M { get; [Provided] set; }}" =? false
        hasDiagnostics "interface C { int M { get; [Required] set; }}" =? false
        hasDiagnostics "interface C { int M { [Provided] get; set; }}" =? false

[<TestFixture>]
module ClassPortAttributeContradictsInterfacePortAttributeAnalyzerTests =
    let hasDiagnostics csharpCode = 
        let csharpCode = "interface I : IComponent { [Required] void In(); [Provided] void Out(); }
            interface J : IComponent { [Required] int In { get; set; } [Provided] int Out { get; set; }}" + csharpCode
        TestCompilation.HasDiagnostics (ClassPortAttributeContradictsInterfacePortAttributeAnalyzer ()) csharpCode

    [<Test>]
    let ``Implementations without attributes are valid`` () =
        hasDiagnostics "class C : Component, I { public void In() {} public void Out() {}}" =? false
        hasDiagnostics "class C : Component, I { void I.In() {} void I.Out() {}}" =? false
        hasDiagnostics "class C : Component, J { public int In { get; set; } public int Out { get; set; }}" =? false
        hasDiagnostics "class C : Component, J { int J.In { get; set; } int J.Out { get; set; }}" =? false

    [<Test>]
    let ``Implementations with wrong attribute outside of component class are valid`` () =
        hasDiagnostics "class C : I { [Provided] public void In() {} [Required] public void Out() {}}" =? false
        hasDiagnostics "class C : I { [Provided] void I.In() {} [Required] void I.Out() {}}" =? false
        hasDiagnostics "class C : J { [Provided] public int In { get; set; } [Required] public int Out { get; set; }}" =? false
        hasDiagnostics "class C : J { [Provided] int J.In { get; set; } [Required] int J.Out { get; set; }}" =? false

    [<Test>]
    let ``Implementations with wrong attribute are valid if interface does not derive from IComponent`` () =
        hasDiagnostics "interface X { [Provided] void T(); } class C : X { [Required] public void T() {}}" =? false
        hasDiagnostics "interface X { [Provided] void T(); } class C : X { [Required] void X.T() {}}" =? false
        hasDiagnostics "interface X { [Provided] void T(); } class C : Component, X { [Required] public void T() {}}" =? false
        hasDiagnostics "interface X { [Provided] void T(); } class C : Component, X { [Required] void X.T() {}}" =? false
        hasDiagnostics "interface X { [Provided] int T { get; set; }} class C : X { [Required] public int T { get; set; }}" =? false
        hasDiagnostics "interface X { [Provided] int T { get; set; }} class C : X { [Required] int X.T { get; set; }}" =? false
        hasDiagnostics "interface X { [Provided] int T { get; set; }} class C : Component, X { [Required] public int T { get; set; }}" =? false
        hasDiagnostics "interface X { [Provided] int T { get; set; }} class C : Component, X { [Required] int X.T { get; set; }}" =? false

    [<Test>]
    let ``Implementations with wrong attribute class are invalid`` () =
        hasDiagnostics "class C : Component, I { [Required] public void In() {} [Required] public void Out() {}}" =? true
        hasDiagnostics "class C : Component, I { [Provided] public void In() {} [Provided] public void Out() {}}" =? true
        hasDiagnostics "class C : Component, I { [Provided] public void In() {} [Required] public void Out() {}}" =? true
        hasDiagnostics "class C : Component, I { [Required] void I.In() {} [Required] void I.Out() {}}" =? true
        hasDiagnostics "class C : Component, I { [Provided] void I.In() {} [Provided] void I.Out() {}}" =? true
        hasDiagnostics "class C : Component, I { [Provided] void I.In() {} [Required] void I.Out() {}}" =? true
        hasDiagnostics "class C : Component, J { [Required] public int In { get; set; } [Required] public int Out { get; set; }}" =? true
        hasDiagnostics "class C : Component, J { [Provided] public int In { get; set; } [Provided] public int Out { get; set; }}" =? true
        hasDiagnostics "class C : Component, J { [Provided] public int In { get; set; } [Required] public int Out { get; set; }}" =? true
        hasDiagnostics "class C : Component, J { [Required] int J.In { get; set; } [Required] int J.Out { get; set; }}" =? true
        hasDiagnostics "class C : Component, J { [Provided] int J.In { get; set; } [Provided] int J.Out { get; set; }}" =? true
        hasDiagnostics "class C : Component, J { [Provided] int J.In { get; set; } [Required] int J.Out { get; set; }}" =? true

[<TestFixture>]
module ExternImplementedProvidedPortAnalyzerTests =
    let hasDiagnostics csharpCode = 
        let csharpCode = "interface I : IComponent { [Provided] void M(); } interface J : IComponent { [Provided] int M { get; set; }}" + csharpCode
        TestCompilation.HasDiagnostics (ExternImplementedProvidedPortAnalyzer ()) csharpCode

    [<Test>]
    let ``Non-extern method or property is valid`` () =
        hasDiagnostics "class C : Component, I { public void M() {}}" =? false
        hasDiagnostics "class C : Component, J { public int M { get; set; }}" =? false

    [<Test>]
    let ``Extern method or property with is invalid`` () =
        hasDiagnostics "class C : Component, I { public extern void M(); }" =? true
        hasDiagnostics "class C : Component, J { public extern int M { get; set; }}" =? true

    [<Test>]
    let ``Extern method or property outside of component classes is valid`` () =
        hasDiagnostics "class C : I { public extern void M();}" =? false
        hasDiagnostics "class C : J { public extern int M { get; set; }}" =? false

    [<Test>]
    let ``Extern method or property outside of component interfaces is valid`` () =
        hasDiagnostics "interface X { [Provided] void M(); } class C : X { public extern void M();}" =? false
        hasDiagnostics "interface X { [Provided] int M { get; set; }} class C : X { public extern int M { get; set; }}" =? false

[<TestFixture>]
module NonExternImplementedRequiredPortAnalyzerTests =
    let hasDiagnostics csharpCode = 
        let csharpCode = "interface I : IComponent { [Required] void M(); } interface J : IComponent { [Required] int M { get; set; }}" + csharpCode
        TestCompilation.HasDiagnostics (NonExternImplementedRequiredPortAnalyzer ()) csharpCode

    [<Test>]
    let ``Non-extern method or property is invalid`` () =
        hasDiagnostics "class C : Component, I { public void M() {}}" =? true
        hasDiagnostics "class C : Component, J { public int M { get; set; }}" =? true

    [<Test>]
    let ``Extern method or property with Required attribute is valid`` () =
        hasDiagnostics "class C : Component, I { public extern void M(); }" =? false
        hasDiagnostics "class C : Component, J { public extern int M { get; set; }}" =? false

    [<Test>]
    let ``Non-extern method or property outside of component classes is valid`` () =
        hasDiagnostics "class C : I { public void M() {}}" =? false
        hasDiagnostics "class C : J { public int M { get; set; }}" =? false

    [<Test>]
    let ``Non-extern method or property outside of component interfaces is valid`` () =
        hasDiagnostics "interface X { [Required] void M(); } class C : X { public void M() {}}" =? false
        hasDiagnostics "interface X { [Required] int M { get; set; }} class C : X { public int M { get; set; }}" =? false