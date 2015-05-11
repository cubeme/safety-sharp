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

namespace Normalization

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Diagnostics
open SafetySharp.Modeling
open SafetySharp.Compiler.Normalization
open SafetySharp.CSharp.Roslyn.Syntax
open SafetySharp.CSharp.Roslyn.Symbols

[<TestFixture>]
module RequiredPortNormalizer =
    let normalize csharpCode = 
        TestCompilation.GetNormalizedClass (RequiredPortNormalizer ()) (sprintf "using System.Diagnostics; %s" csharpCode)

    [<Test>]
    let ``does not normalize extern method not declared within a component class`` () =
        normalize "class X { extern void M(); }" =? "class X { extern void M(); }"

    [<Test>]
    let ``does not normalize non-extern component method`` () =
        normalize "class X : Component { public void M() {}}" =? "class X : Component { public void M() {}}"

    [<Test>]
    let ``normalizes extern 'void -> void' method within a component`` () =
        let normalized = sprintf "\
            class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] %s void M() => this.__reqPortField0__();}"

        normalize "class X : Component { public extern void M(); }" =? normalized "public"
        normalize "class X : Component { internal extern void M(); }" =? normalized "internal"
        normalize "class X : Component { protected internal extern void M(); }" =? normalized "protected internal"
        normalize "class X : Component { protected extern void M(); }" =? normalized "protected"
        normalize "class X : Component { private extern void M(); }" =? normalized "private"

    [<Test>]
    let ``normalizes extern void returning method within a component`` () =
        normalize "class X : Component { public extern void M(int a); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate0__(int a);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] public void M(int a) => this.__reqPortField0__(a);}"

        normalize "class X : Component { internal extern void M(int a, decimal b); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate0__(int a, decimal b);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] internal void M(int a, decimal b) => this.__reqPortField0__(a, b);}"

        normalize "class X : Component { internal extern void M(int a, decimal b, bool c); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate0__(int a, decimal b, bool c);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] internal void M(int a, decimal b, bool c) => this.__reqPortField0__(a, b, c);}"

    [<Test>]
    let ``normalizes extern method within params, ref, and out parameters`` () =
        normalize "class X : Component { public extern void M(ref int a, out bool b); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate0__(ref int a, out bool b);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] public void M(ref int a, out bool b) => this.__reqPortField0__(ref a, out b);}"

        normalize "class X : Component { internal extern void M(params int[] a); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate0__(params int[] a);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] internal void M(params int[] a) => this.__reqPortField0__(a);}"

    [<Test>]
    let ``normalizes extern non-void returning method within a component`` () =
        normalize "class X : Component { public extern bool M(int a); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate bool __ReqPortDelegate0__(int a);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] public bool M(int a) => this.__reqPortField0__(a);}"

        normalize "class X : Component { internal extern int M(int a, decimal b); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate int __ReqPortDelegate0__(int a, decimal b);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] internal int M(int a, decimal b) => this.__reqPortField0__(a, b);}"

        normalize "class X : Component { internal extern bool M(int a, decimal b, bool c); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate bool __ReqPortDelegate0__(int a, decimal b, bool c);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] internal bool M(int a, decimal b, bool c) => this.__reqPortField0__(a, b, c);}"

    [<Test>]
    let ``normalizes multiple required ports`` () =
        normalize "class X : Component { public extern bool M(int a);\npublic extern void M(); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate bool __ReqPortDelegate0__(int a);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] public bool M(int a) => this.__reqPortField0__(a);\n\
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate1__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate1__ __reqPortField1__;\
            [SafetySharp.Modeling.RequiredAttribute()] public void M() => this.__reqPortField1__();}"

    [<Test>]
    let ``normalizes explictly implemented extern method within a component`` () =
        normalize "namespace A.B.C { interface I { void M(); }} class X : Component, A.B.C.I { extern void A.B.C.I.M(); }" =?
            "class X : Component, A.B.C.I { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] void A.B.C.I.M() => this.__reqPortField0__();}"

    [<Test>]
    let ``preserves attributes applied to extern method within a component`` () =
        let normalized = sprintf "\
            class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            %s [SafetySharp.Modeling.RequiredAttribute()] void M() => this.__reqPortField0__();}"

        normalize "class X : Component { [DebuggerHidden] extern void M(); }" =? normalized "[DebuggerHidden]"
        normalize "class X : Component { [DebuggerHidden, DebuggerNonUserCode] extern void M(); }" =? normalized "[DebuggerHidden, DebuggerNonUserCode]"
        normalize "class X : Component { [DebuggerHidden] [DebuggerNonUserCode] extern void M(); }" =? normalized "[DebuggerHidden] [DebuggerNonUserCode]"

    [<Test>]
    let ``preserves line numbers of following lines`` () =
        let actual = normalize "class X : Component { public \nextern\n void M(int a,\nint b,\nint c); \n\nint f; }" |> normalizeNewLines
        let expected = 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate0__(int a, int b, int c);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] public void M(int a, int b, int c) => this.__reqPortField0__(a, b, c);\n\n\n\n\n\nint f; }"

        actual =? expected

    [<Test>]
    let ``normalizes required port of component class nested in other component class`` () =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree (RequiredPortNormalizer()) "class Y : Component { class X : Component { public extern void M(); }}"
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single(fun c -> c.Identifier.ValueText = "X").ToFullString () =?  
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] public void M() => this.__reqPortField0__();}"

    [<Test>]
    let ``normalizes required port of component class nested in other non-component class`` () =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree (RequiredPortNormalizer()) "class Y { class X : Component { public extern void M(); }}"
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single(fun c -> c.Identifier.ValueText = "X").ToFullString () =?  
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] public void M() => this.__reqPortField0__();}"

    [<Test>]
    let ``does not normalize Update method`` () =
        normalize "class X : Component { public override void Update() {} }" =? "class X : Component { public override void Update() {} }"

    [<Test>]
    let ``normalizes replaced Update method`` () =
        normalize "class X : Component { public new extern void Update(); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] public new void Update() => this.__reqPortField0__();}"

    [<Test>]
    let ``does not get confused by comments`` () =
        normalize "class X : Component { //TODO\nextern void M(); }" =? 
            "class X : Component { //TODO\n\
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] void M() => this.__reqPortField0__();}"

        normalize "class X : Component { ///<summary>X</summary>\nextern void M(); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            ///<summary>X</summary>\n[SafetySharp.Modeling.RequiredAttribute()] void M() => this.__reqPortField0__();}"

        normalize "class X : Component { void N() {}\n///<summary>\n///X\n///</summary>\n//TODO\npublic extern void M(); }" =? 
            "class X : Component { void N() {}\n\
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __ReqPortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __ReqPortDelegate0__ __reqPortField0__;\
            ///<summary>\n///X\n///</summary>\n//TODO\n[SafetySharp.Modeling.RequiredAttribute()] public void M() => this.__reqPortField0__();}"