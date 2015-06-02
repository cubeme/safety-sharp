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
module PortNormalizer =
    let normalize csharpCode = 
        TestCompilation.GetNormalizedClass (PortNormalizer ()) (sprintf "using System.Diagnostics; %s" csharpCode)

    [<Test>]
    let ``does not normalize extern method not declared within a component class`` () =
        normalize "class X { extern void M(); }" =? "class X { extern void M(); }"
        normalize "class X { void M() {} }" =? "class X { void M() {} }"

    [<Test>]
    let ``does not normalize static methods`` () =
        normalize "class X : Component { static extern void M(); }" =? "class X : Component { static extern void M(); }"
        normalize "class X : Component { static void M() {} }" =? "class X : Component { static void M() {} }"

    [<Test>]
    let ``normalizes extern 'void -> void' method within a component`` () =
        let normalized = sprintf "\
            class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] %s void M() => this.__portField0__();}"

        normalize "class X : Component { public extern void M(); }" =? normalized "public"
        normalize "class X : Component { internal extern void M(); }" =? normalized "internal"
        normalize "class X : Component { protected internal extern void M(); }" =? normalized "protected internal"
        normalize "class X : Component { protected extern void M(); }" =? normalized "protected"
        normalize "class X : Component { private extern void M(); }" =? normalized "private"

    [<Test>]
    let ``normalizes extern void returning method within a component`` () =
        normalize "class X : Component { public extern void M(int a); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__(int a);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] public void M(int a) => this.__portField0__(a);}"

        normalize "class X : Component { internal extern void M(int a, decimal b); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__(int a, decimal b);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] internal void M(int a, decimal b) => this.__portField0__(a, b);}"

        normalize "class X : Component { internal extern void M(int a, decimal b, bool c); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__(int a, decimal b, bool c);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] internal void M(int a, decimal b, bool c) => this.__portField0__(a, b, c);}"

    [<Test>]
    let ``normalizes extern method within params, ref, and out parameters`` () =
        normalize "class X : Component { public extern void M(ref int a, out bool b); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__(ref int a, out bool b);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] public void M(ref int a, out bool b) => this.__portField0__(ref a, out b);}"

        normalize "class X : Component { internal extern void M(params int[] a); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__(params int[] a);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] internal void M(params int[] a) => this.__portField0__(a);}"

    [<Test>]
    let ``normalizes extern non-void returning method within a component`` () =
        normalize "class X : Component { public extern bool M(int a); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate bool __PortDelegate0__(int a);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] public bool M(int a) => this.__portField0__(a);}"

        normalize "class X : Component { internal extern int M(int a, decimal b); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate int __PortDelegate0__(int a, decimal b);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] internal int M(int a, decimal b) => this.__portField0__(a, b);}"

        normalize "class X : Component { internal extern bool M(int a, decimal b, bool c); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate bool __PortDelegate0__(int a, decimal b, bool c);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] internal bool M(int a, decimal b, bool c) => this.__portField0__(a, b, c);}"

    [<Test>]
    let ``normalizes multiple required ports`` () =
        normalize "class X : Component { public extern bool M(int a);\npublic extern void M(); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate bool __PortDelegate0__(int a);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] public bool M(int a) => this.__portField0__(a);\n\
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate1__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate1__ __portField1__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField1__\")] public void M() => this.__portField1__();}"

    [<Test>]
    let ``normalizes explictly implemented extern method within a component`` () =
        normalize "namespace A.B.C { interface I { void M(); }} class X : Component, A.B.C.I { extern void A.B.C.I.M(); }" =?
            "class X : Component, A.B.C.I { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void A.B.C.I.M() => this.__portField0__();}"

    [<Test>]
    let ``preserves attributes applied to extern method within a component`` () =
        let normalized = sprintf "\
            class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            %s [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void M() => this.__portField0__();}"

        normalize "class X : Component { [DebuggerHidden] extern void M(); }" =? normalized "[DebuggerHidden]"
        normalize "class X : Component { [DebuggerHidden, DebuggerNonUserCode] extern void M(); }" =? normalized "[DebuggerHidden, DebuggerNonUserCode]"
        normalize "class X : Component { [DebuggerHidden] [DebuggerNonUserCode] extern void M(); }" =? normalized "[DebuggerHidden] [DebuggerNonUserCode]"

    [<Test>]
    let ``preserves line numbers of following lines`` () =
        let actual = normalize "class X : Component { public \nextern\n void M(int a,\nint b,\nint c); \n\nint f; }" |> normalizeNewLines
        let expected = 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__(int a, int b, int c);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] public void M(int a, int b, int c) => this.__portField0__(a, b, c);\n\n\n\n\n\nint f; }"

        actual =? expected

    [<Test>]
    let ``normalizes required port of component class nested in other component class`` () =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree (PortNormalizer()) "class Y : Component { class X : Component { public extern void M(); } public extern void N(); }"
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single(fun c -> c.Identifier.ValueText = "Y").ToFullString () =?  
            "class Y : Component { class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] public void M() => this.__portField0__();} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate1__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate1__ __portField1__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField1__\")] public void N() => this.__portField1__();}"

    [<Test>]
    let ``normalizes required port of component class nested in other non-component class`` () =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree (PortNormalizer()) "class Y { class X : Component { public extern void M(); }}"
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single(fun c -> c.Identifier.ValueText = "X").ToFullString () =?  
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] public void M() => this.__portField0__();}"

    [<Test>]
    let ``does not normalize Update method`` () =
        normalize "class X : Component { public override void Update() {} }" =? "class X : Component { public override void Update() {} }"

    [<Test>]
    let ``does not normalize abstract method with provided attribute`` () =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree (PortNormalizer()) "abstract class X : Component { [Provided] public abstract void M(); }"
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single(fun c -> c.Identifier.ValueText = "X").ToFullString () =?  
            "abstract class X : Component { [Provided] public abstract void M(); }"

    [<Test>]
    let ``only adds provided attribute to abstract method`` () =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree (PortNormalizer()) "abstract class X : Component { public abstract void M(); }"
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single(fun c -> c.Identifier.ValueText = "X").ToFullString () =?  
            "abstract class X : Component { [SafetySharp.Modeling.ProvidedAttribute()] public abstract void M(); }"

    [<Test>]
    let ``normalizes Update method replaced by required port`` () =
        normalize "class X : Component { public new extern void Update(); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] public new void Update() => this.__portField0__();}"

    [<Test>]
    let ``does not get confused by comments`` () =
        normalize "class X : Component { //TODO\nextern void M(); }" =? 
            "class X : Component { //TODO\n\
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void M() => this.__portField0__();}"

        normalize "class X : Component { ///<summary>X</summary>\nextern void M(); }" =? 
            "class X : Component { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            ///<summary>X</summary>\n[SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void M() => this.__portField0__();}"

        normalize "class X : Component { int i; \n///<summary>\n///X\n///</summary>\n//TODO\npublic extern void M(); }" =? 
            "class X : Component { int i; \n\
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            ///<summary>\n///X\n///</summary>\n//TODO\n[SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] public void M() => this.__portField0__();}"

    [<Test>]
    let ``normalizes Update method replaced by provided port`` () =
        normalize "class X : Component { public new void Update() {} }" =? 
            "class X : Component { \
            private void __DefaultImplementation0__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] public new void Update() => this.__portField0__();}"

    [<Test>]
    let ``documentation comments are placed correctly on provided port`` () =
        normalize "class X : Component { ///<summary>X</summary>\npublic void M() {} }" =? 
            "class X : Component { \
            ///<summary>X</summary>\nprivate void __DefaultImplementation0__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] public void M() => this.__portField0__();}"

    [<Test>]
    let ``normalizes provided port with implicit private accessibility`` () =
        normalize "class X : Component { void M() {} }" =? 
            "class X : Component { \
            private void __DefaultImplementation0__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void M() => this.__portField0__();}"

    [<Test>]
    let ``normalizes provided port with protected internal accessibility and trivia`` () =
        normalize "class X : Component { \nprotected\n\ninternal\nvoid M() {} }" =? 
            "class X : Component { \
            \n\nprivate\n\nvoid __DefaultImplementation0__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] protected internal void M() => this.__portField0__();}"

    [<Test>]
    let ``normalizes virtual provided port`` () =
        normalize "class X : Component { public virtual void M() {} }" =? 
            "class X : Component { \
            private void __DefaultImplementation0__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] public virtual void M() => this.__portField0__();}"

    [<Test>]
    let ``normalizes overridden provided port`` () =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree (PortNormalizer()) "class Y : Component { public virtual void M() {}} class X : Y { public override void M() {} }"
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single(fun c -> c.Identifier.ValueText = "X").ToFullString () =?  
            "class X : Y { \
            private void __DefaultImplementation1__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate1__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate1__ __portField1__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation1__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField1__\")] public override void M() => this.__portField1__();}"

    [<Test>]
    let ``normalizes overridden sealed provided port`` () =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree (PortNormalizer()) "class Y : Component { public virtual void M() {}} class X : Y { public override sealed void M() {} }"
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single(fun c -> c.Identifier.ValueText = "X").ToFullString () =?  
            "class X : Y { \
            private void __DefaultImplementation1__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate1__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate1__ __portField1__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation1__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField1__\")] public override sealed void M() => this.__portField1__();}"

    [<Test>]
    let ``normalizes replaced provided port`` () =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree (PortNormalizer()) "class Y : Component { public virtual void M() {}} class X : Y { public new void M() {} }"
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single(fun c -> c.Identifier.ValueText = "X").ToFullString () =?  
            "class X : Y { \
            private void __DefaultImplementation1__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate1__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate1__ __portField1__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation1__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField1__\")] public new void M() => this.__portField1__();}"

    [<Test>]
    let ``does not change attribute of component method that is already marked with the attribute`` () =
        normalize "class X : Component { [Provided] void M() {} }" =? 
            "class X : Component { \
            [Provided] private void __DefaultImplementation0__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [Provided] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void M() => this.__portField0__();}"

    [<Test>]
    let ``normalizes provided port of component`` () =
        normalize "class X : Component { void M() {} }" =?
            "class X : Component { \
            private void __DefaultImplementation0__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void M() => this.__portField0__();}"

        normalize "class X : Component { protected void M() {} }" =? 
            "class X : Component { \
            private void __DefaultImplementation0__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] protected void M() => this.__portField0__();}"

    [<Test>]
    let ``normalizes explicitly implemented provided port of component`` () =
        normalize "namespace Q { interface I { void M(); }} class X : Component, Q.I { void Q.I.M() {} }" =? 
            "class X : Component, Q.I { \
            private void __DefaultImplementation0__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void Q.I.M() => this.__portField0__();}"

        normalize "namespace Q { interface I<T> { void M(T t); }} class X : Component, Q.I<int> { void Q.I<int>.M(int t) {} }" =? 
            "class X : Component, Q.I<int> { \
            private void __DefaultImplementation0__(int t) {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__(int t);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void Q.I<int>.M(int t) => this.__portField0__(t);}"

    [<Test>]
    let ``normalizes explicitly implemented required port of component`` () =
        normalize "namespace Q { interface I { [Required] void M(); }} class X : Component, Q.I { extern void Q.I.M(); }" =? 
            "class X : Component, Q.I { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void Q.I.M() => this.__portField0__();}"

        normalize "namespace Q { interface I<T> { [Required] void M(T t); }} class X : Component, Q.I<int> { extern void Q.I<int>.M(int t); }" =? 
            "class X : Component, Q.I<int> { \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__(int t);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.RequiredAttribute()] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void Q.I<int>.M(int t) => this.__portField0__(t);}"

    [<Test>]
    let ``normalizes multiple provided ports of component`` () =
        normalize "class X : Component { void M() {} void N() {} }" =?
            "class X : Component { \
            private void __DefaultImplementation0__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void M() => this.__portField0__();\
            private void __DefaultImplementation1__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate1__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate1__ __portField1__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation1__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField1__\")] void N() => this.__portField1__();}"

    [<Test>]
    let ``normalizes provided port of component and keeps all attributes`` () =
        normalize "class X : Component { [DebuggerHidden] void M() {} }" =? 
            "class X : Component { \
            [DebuggerHidden] private void __DefaultImplementation0__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [DebuggerHidden] [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void M() => this.__portField0__();}"
        
        normalize "class X : Component { [DebuggerHidden, DebuggerNonUserCode] void M() {} }" =? 
            "class X : Component { \
            [DebuggerHidden, DebuggerNonUserCode] private void __DefaultImplementation0__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [DebuggerHidden, DebuggerNonUserCode] [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void M() => this.__portField0__();}"
        
        normalize "class X : Component { [DebuggerHidden] [DebuggerNonUserCode] void M() {} }" =? 
            "class X : Component { \
            [DebuggerHidden] [DebuggerNonUserCode] private void __DefaultImplementation0__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [DebuggerHidden] [DebuggerNonUserCode] [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void M() => this.__portField0__();}"

    [<Test>]
    let ``normalizes provided port of component class nested in other component class`` () =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree (PortNormalizer()) "class Y : Component { class X : Component { void M() {} }}"
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single(fun c -> c.Identifier.ValueText = "X").ToFullString () =?  
            "class X : Component { \
            private void __DefaultImplementation0__() {} \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __PortDelegate0__();\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] void M() => this.__portField0__();}"

    [<Test>]
    let ``normalizes provided port of component class nested in other non-component class`` () =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree (PortNormalizer()) "class Y { class X : Component { int M(int i) { return i; } }}"
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single(fun c -> c.Identifier.ValueText = "X").ToFullString () =?  
            "class X : Component { \
            private int __DefaultImplementation0__(int i) { return i; } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate int __PortDelegate0__(int i);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] int M(int i) => this.__portField0__(i);}"

        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree (PortNormalizer()) "class Y { class X : Component { int M(int i) \n=>\n 1; }}"
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single(fun c -> c.Identifier.ValueText = "X").ToFullString () =?  
            "class X : Component { \
            private int __DefaultImplementation0__(int i) \n=>\n 1; \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate int __PortDelegate0__(int i);\
            [System.Diagnostics.DebuggerBrowsableAttribute(System.Diagnostics.DebuggerBrowsableState.Never)] [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private __PortDelegate0__ __portField0__;\
            [SafetySharp.Modeling.ProvidedAttribute()] [SafetySharp.Modeling.DefaultImplementationAttribute(\"__DefaultImplementation0__\")] [SafetySharp.Modeling.BackingFieldAttribute(\"__portField0__\")] int M(int i) => this.__portField0__(i);}"
