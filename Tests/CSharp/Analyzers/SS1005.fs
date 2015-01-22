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

namespace Analyzers

open System
open System.Linq
open NUnit.Framework
open SafetySharp.CSharpCompiler.Analyzers
open SafetySharp.CSharpCompiler.Roslyn.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols

[<TestFixture>]
module SS1005 =
    let getDiagnostic csharpCode = 
        let csharpCode = 
            "interface I : IComponent { [Required] void In(); [Provided] void Out(); }
            interface J : IComponent { [Required] int In { get; set; } [Provided] int Out { get; set; }}\n" 
            + csharpCode
        TestCompilation.GetDiagnostic (SS1005 ()) csharpCode

    let ss1005 location length memberName interfaceMemberName declaredPortType actualPortType =
        Diagnostic ("SS1005", (3, location), (3, location + length), 
            sprintf "'%s' does not implement interface member '%s'. '%s' is declared as a %s port, but is implemented as a %s port." 
                    memberName interfaceMemberName interfaceMemberName declaredPortType actualPortType)
        |> Some

    [<Test>]
    let ``Implementations without attributes are valid`` () =
        getDiagnostic "class C : Component, I { public extern void In(); public void Out() {}}" =? None
        getDiagnostic "class C : Component, I { extern void I.In(); void I.Out() {}}" =? None
        getDiagnostic "class C : Component, J { public extern int In { get; set; } public int Out { get; set; }}" =? None
        getDiagnostic "class C : Component, J { extern int J.In { get; set; } int J.Out { get; set; }}" =? None

    [<Test>]
    let ``Implementations with wrong attribute outside of component class are valid`` () =
        getDiagnostic "class C : I { public void Update() {} [Provided] public void In() {} [Required] extern public void Out(); }" =? None
        getDiagnostic "class C : I { public void Update() {} [Provided] void I.In() {} [Required] extern void I.Out(); }" =? None
        getDiagnostic "class C : J { public void Update() {} [Provided] public int In { get; set; } [Required] extern public int Out { get; set; }}" =? None
        getDiagnostic "class C : J { public void Update() {} [Provided] int J.In { get; set; } [Required] extern int J.Out { get; set; }}" =? None

    [<Test>]
    let ``Implementations with wrong attribute are valid if interface does not derive from IComponent`` () =
        getDiagnostic "interface X { [Provided] void T(); } class C : X { [Required] public void T() {}}" =? None
        getDiagnostic "interface X { [Provided] void T(); } class C : X { [Required] void X.T() {}}" =? None
        getDiagnostic "interface X { [Provided] void T(); } class C : Component, X { [Required] public void T() {}}" =? None
        getDiagnostic "interface X { [Provided] void T(); } class C : Component, X { [Required] void X.T() {}}" =? None
        getDiagnostic "interface X { [Provided] int T { get; set; }} class C : X { [Required] public int T { get; set; }}" =? None
        getDiagnostic "interface X { [Provided] int T { get; set; }} class C : X { [Required] int X.T { get; set; }}" =? None
        getDiagnostic "interface X { [Provided] int T { get; set; }} class C : Component, X { [Required] public int T { get; set; }}" =? None
        getDiagnostic "interface X { [Provided] int T { get; set; }} class C : Component, X { [Required] int X.T { get; set; }}" =? None

    [<Test>]
    let ``Implementations with wrong port type are invalid`` () =
        getDiagnostic "class C : Component, I { extern public void In(); extern public void Out(); }" 
            =? ss1005 69 3 "C.Out()" "I.Out()" "provided" "required"
        getDiagnostic "class C : Component, I { [Provided] public void In() {} [Provided] public void Out() {}}" 
            =? ss1005 48 2 "C.In()" "I.In()" "required" "provided"
        getDiagnostic "class C : Component, I { extern void I.In(); extern void I.Out(); }" 
            =? ss1005 59 3 "C.I.Out()" "I.Out()" "provided" "required"
        getDiagnostic "class C : Component, I { [Provided] void I.In() {} [Provided] void I.Out() {}}" 
            =? ss1005 43 2 "C.I.In()" "I.In()" "required" "provided"
        getDiagnostic "class C : Component, J { extern public int In { get; set; } [Required] extern public int Out { get; set; }}" 
            =? ss1005 89 3 "C.Out" "J.Out" "provided" "required"
        getDiagnostic "class C : Component, J { [Provided] public int In { get; set; } [Provided] public int Out { get; set; }}" 
            =? ss1005 47 2 "C.In" "J.In" "required" "provided"
        getDiagnostic "class C : Component, J { extern int J.In { get; set; } [Required] extern int J.Out { get; set; }}"  
            =? ss1005 79 3 "C.J.Out" "J.Out" "provided" "required"
        getDiagnostic "class C : Component, J { [Provided] int J.In { get; set; } [Provided] int J.Out { get; set; }}" 
            =? ss1005 42 2 "C.J.In" "J.In" "required" "provided"

    [<Test>]
    let ``Implementations of interface members in base class with wrong port type are invalid`` () =
        getDiagnostic "class C : Component { extern public void In(); extern public void Out(); } class X : C, I {}" 
            =? ss1005 66 3 "C.Out()" "I.Out()" "provided" "required"
        getDiagnostic "class C : Component { [Provided] public void In() {} [Provided] public void Out() {}} class X : C, I {}" 
            =? ss1005 45 2 "C.In()" "I.In()" "required" "provided"
        getDiagnostic "class C : Component { extern public int In { get; set; } [Required] extern public int Out { get; set; }} class X : C, J {}" 
            =? ss1005 86 3 "C.Out" "J.Out" "provided" "required"
        getDiagnostic "class C : Component { [Provided] public int In { get; set; } [Provided] public int Out { get; set; }} class X : C, J {}" 
            =? ss1005 44 2 "C.In" "J.In" "required" "provided"

    [<Test>]
    let ``Implementations with unknown port type are ignored`` () =
        getDiagnostic "class C : Component, I { [Provided] extern public void In(); [Required] public void Out() {}}" =? None
        getDiagnostic "class C : Component, J { [Provided] extern public int In { get; set; } [Required] public int Out { get; set; }}" =? None

    [<Test>]
    let ``Implementations of interface members with unknown port type are ignored`` () =
        getDiagnostic "interface I2 { int X(); } class C : I2 { public int X() { return 1; }}" =? None
        getDiagnostic "interface I2 { int X { get; } } class C : I2 { public int X { get { return 1; } }}" =? None