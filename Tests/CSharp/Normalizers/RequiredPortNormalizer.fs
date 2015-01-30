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
            public delegate void __M____Delegate__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __M____Delegate__ __M____Field__;\
            [SafetySharp.Modeling.RequiredAttribute()] %s void M() => this.__M____Field__();}"

        normalize "class X : Component { public extern void M(); }" =? normalized "public"
        normalize "class X : Component { internal extern void M(); }" =? normalized "internal"
        normalize "class X : Component { protected internal extern void M(); }" =? normalized "protected internal"
        normalize "class X : Component { protected extern void M(); }" =? normalized "protected"
        normalize "class X : Component { private extern void M(); }" =? normalized "private"

    [<Test>]
    let ``normalizes extern void returning method within a component`` () =
        normalize "class X : Component { public extern void M(int a); }" =? 
            "class X : Component { \
            public delegate void __M__int__Delegate__(int a);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __M__int__Delegate__ __M__int__Field__;\
            [SafetySharp.Modeling.RequiredAttribute()] public void M(int a) => this.__M__int__Field__(a);}"

        normalize "class X : Component { internal extern void M(int a, decimal b); }" =? 
            "class X : Component { \
            public delegate void __M__int__decimal__Delegate__(int a, decimal b);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __M__int__decimal__Delegate__ __M__int__decimal__Field__;\
            [SafetySharp.Modeling.RequiredAttribute()] internal void M(int a, decimal b) => this.__M__int__decimal__Field__(a, b);}"

        normalize "class X : Component { internal extern void M(int a, decimal b, bool c); }" =? 
            "class X : Component { \
            public delegate void __M__int__decimal__bool__Delegate__(int a, decimal b, bool c);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __M__int__decimal__bool__Delegate__ __M__int__decimal__bool__Field__;\
            [SafetySharp.Modeling.RequiredAttribute()] internal void M(int a, decimal b, bool c) => this.__M__int__decimal__bool__Field__(a, b, c);}"

    [<Test>]
    let ``normalizes extern method within params, ref, and out parameters`` () =
        normalize "class X : Component { public extern void M(ref int a, out bool b); }" =? 
            "class X : Component { \
            public delegate void __M__ref_int__out_bool__Delegate__(ref int a, out bool b);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __M__ref_int__out_bool__Delegate__ __M__ref_int__out_bool__Field__;\
            [SafetySharp.Modeling.RequiredAttribute()] public void M(ref int a, out bool b) => this.__M__ref_int__out_bool__Field__(ref a, out b);}"

        normalize "class X : Component { internal extern void M(params int[] a); }" =? 
            "class X : Component { \
            public delegate void __M__params_int_a__Delegate__(params int[] a);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __M__params_int_a__Delegate__ __M__params_int_a__Field__;\
            [SafetySharp.Modeling.RequiredAttribute()] internal void M(params int[] a) => this.__M__params_int_a__Field__(a);}"

    [<Test>]
    let ``normalizes extern non-void returning method within a component`` () =
        normalize "class X : Component { public extern bool M(int a); }" =? 
            "class X : Component { \
            public delegate bool __M__int__Delegate__(int a);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __M__int__Delegate__ __M__int__Field__;\
            [SafetySharp.Modeling.RequiredAttribute()] public bool M(int a) => this.__M__int__Field__(a);}"

        normalize "class X : Component { internal extern int M(int a, decimal b); }" =? 
            "class X : Component { \
            public delegate int __M__int__decimal__Delegate__(int a, decimal b);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __M__int__decimal__Delegate__ __M__int__decimal__Field__;\
            [SafetySharp.Modeling.RequiredAttribute()] internal int M(int a, decimal b) => this.__M__int__decimal__Field__(a, b);}"

        normalize "class X : Component { internal extern bool M(int a, decimal b, bool c); }" =? 
            "class X : Component { \
            public delegate bool __M__int__decimal__bool__Delegate__(int a, decimal b, bool c);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __M__int__decimal__bool__Delegate__ __M__int__decimal__bool__Field__;\
            [SafetySharp.Modeling.RequiredAttribute()] internal bool M(int a, decimal b, bool c) => this.__M__int__decimal__bool__Field__(a, b, c);}"

    [<Test>]
    let ``normalizes multiple required ports`` () =
        normalize "class X : Component { public extern bool M(int a);\npublic extern void M(); }" =? 
            "class X : Component { \
            public delegate bool __M__int__Delegate__(int a);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __M__int__Delegate__ __M__int__Field__;\
            [SafetySharp.Modeling.RequiredAttribute()] public bool M(int a) => this.__M__int__Field__(a);\n\
            public delegate void __M____Delegate__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __M____Delegate__ __M____Field__;\
            [SafetySharp.Modeling.RequiredAttribute()] public void M() => this.__M____Field__();}"

    [<Test>]
    let ``normalizes explictly implemented extern method within a component`` () =
        normalize "namespace A.B.C { interface I { void M(); }} class X : Component, A.B.C.I { extern void A.B.C.I.M(); }" =?
            "class X : Component, A.B.C.I { \
            public delegate void __A_B_C_I_M____Delegate__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __A_B_C_I_M____Delegate__ __A_B_C_I_M____Field__;\
            [SafetySharp.Modeling.RequiredAttribute()] void A.B.C.I.M() => this.__A_B_C_I_M____Field__();}"

    [<Test>]
    let ``preserves attributes applied to extern method within a component`` () =
        let normalized = sprintf "\
            class X : Component { \
            public delegate void __M____Delegate__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __M____Delegate__ __M____Field__;\
            %s [SafetySharp.Modeling.RequiredAttribute()] void M() => this.__M____Field__();}"

        normalize "class X : Component { [DebuggerHidden] extern void M(); }" =? normalized "[DebuggerHidden]"
        normalize "class X : Component { [DebuggerHidden, DebuggerNonUserCode] extern void M(); }" =? normalized "[DebuggerHidden, DebuggerNonUserCode]"
        normalize "class X : Component { [DebuggerHidden] [DebuggerNonUserCode] extern void M(); }" =? normalized "[DebuggerHidden] [DebuggerNonUserCode]"

    [<Test>]
    let ``preserves line numbers of following lines`` () =
        let actual = normalize "class X : Component { public extern void M(int a,\nint b,\nint c); \n\nint f; }" |> normalizeNewLines
        let expected = 
            "class X : Component { \
            public delegate void __M__int__int__int__Delegate__(int a, int b, int c);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __M__int__int__int__Delegate__ __M__int__int__int__Field__;\
            [SafetySharp.Modeling.RequiredAttribute()] public void M(int a, int b, int c) => this.__M__int__int__int__Field__(a, b, c);\n\n\n\nint f; }"

        actual =? expected

    [<Test>]
    let ``normalizes required port of component class nested in other component class`` () =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree (RequiredPortNormalizer()) "class Y : Component { class X : Component { public extern void M(); }}"
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single(fun c -> c.Identifier.ValueText = "X").ToFullString () =?  
            "class X : Component { \
            public delegate void __M____Delegate__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __M____Delegate__ __M____Field__;\
            [SafetySharp.Modeling.RequiredAttribute()] public void M() => this.__M____Field__();}"

    [<Test>]
    let ``normalizes required port of component class nested in other non-component class`` () =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree (RequiredPortNormalizer()) "class Y { class X : Component { public extern void M(); }}"
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single(fun c -> c.Identifier.ValueText = "X").ToFullString () =?  
            "class X : Component { \
            public delegate void __M____Delegate__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] private __M____Delegate__ __M____Field__;\
            [SafetySharp.Modeling.RequiredAttribute()] public void M() => this.__M____Field__();}"