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
module BindingNormalizer =
    let normalize csharpCode = 
        TestCompilation.GetNormalizedClass (BindingNormalizer ()) csharpCode 

    [<Test>]
    let ``normalizes binding of ports of field subcomponent`` () =
        normalize "class X : Component { X x; void M() {} extern void N(); X() { BindDelayed(x.RequiredPorts.N = x.ProvidedPorts.M); } }" =?
            "class X : Component { X x; void M() {} extern void N(); X() { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.M)))); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"

    [<Test>]
    let ``normalizes binding of ports of parameter subcomponent`` () =
        normalize "class X : Component { void M(ref int i) {} extern void N(ref int i); X(X x, X y) { BindDelayed(x.RequiredPorts.N = y.ProvidedPorts.M); } }" =?
            "class X : Component { void M(ref int i) {} extern void N(ref int i); X(X x, X y) { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(y.M)))); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__(ref int i);}"

    [<Test>]
    let ``normalizes binding of ports of local variable subcomponent`` () =
        normalize "class X : Component { void M() {} extern void N(); X() { X x = null; BindDelayed(x.RequiredPorts.N = x.ProvidedPorts.M); } }" =?
            "class X : Component { void M() {} extern void N(); X() { X x = null; BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.M)))); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"

    [<Test>]
    let ``normalizes binding of ports of property subcomponent`` () =
        normalize "class X : Component { X x { get; set; } void M() {} extern void N(); X() { BindDelayed(x.RequiredPorts.N = x.ProvidedPorts.M); } }" =?
            "class X : Component { X x { get; set; } void M() {} extern void N(); X() { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.M)))); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"

    [<Test>]
    let ``normalizes binding of ports of method returned subcomponent`` () =
        normalize "class X : Component { X x() { return null; } void M() {} extern void N(); X() { BindDelayed(x().RequiredPorts.N = x().ProvidedPorts.M); } }" =?
            "class X : Component { X x() { return null; } void M() {} extern void N(); X() { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x().N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x().M)))); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"

    [<Test>]
    let ``normalizes binding of ports of nested subcomponents`` () =
        normalize "interface I : IComponent { [Provided] void M(); [Required] void N(); } class X : Component { I i; X x() { return null; } X() { BindDelayed(x().i.RequiredPorts.N = x().i.ProvidedPorts.M); } }" =?
            "class X : Component { I i; X x() { return null; } X() { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x().i.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x().i.M)))); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"

    [<Test>]
    let ``normalizes binding of self-declared ports`` () =
        normalize "class X : Component { void M() {} extern void N(); X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); } }" =?
            "class X : Component { void M() {} extern void N(); X() { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(M)))); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"

        normalize "class X : Component { void M() {} extern void N(); X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); } }" =?
            "class X : Component { void M() {} extern void N(); X() { BindInstantaneous(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(M)))); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"

    [<Test>]
    let ``normalizes multiple bindings in same constructor`` () =
        normalize "class X : Component { void M() {} int P() { return 1; } extern void N(); extern int Q(); X(X x, X y) { BindDelayed(x.RequiredPorts.N = y.ProvidedPorts.M); BindInstantaneous(x.RequiredPorts.Q = y.ProvidedPorts.P); } }" =?
            "class X : Component { void M() {} int P() { return 1; } extern void N(); extern int Q(); X(X x, X y) { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(y.M)))); \
            BindInstantaneous(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate1__)(x.Q)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate1__)(y.P)))); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();\
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate int __BindingDelegate1__();}"

    [<Test>]
    let ``normalizes multiple bindings in different constructors`` () =
        normalize "class X : Component { void M() {} int P() { return 1; } extern void N(); extern int Q(); X(X x, X y) { BindDelayed(x.RequiredPorts.N = y.ProvidedPorts.M); } X(X x) { BindInstantaneous(x.RequiredPorts.Q = x.ProvidedPorts.P); } }" =?
            "class X : Component { void M() {} int P() { return 1; } extern void N(); extern int Q(); X(X x, X y) { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(y.M)))); } \
            X(X x) { BindInstantaneous(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate1__)(x.Q)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate1__)(x.P)))); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();\
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate int __BindingDelegate1__();}"

    [<Test>]
    let ``normalizes disambiguated binding`` () =
        normalize "class X : Component { void M() {} extern void N(); void M(int i) {} extern void N(int i); X() { BindDelayed(RequiredPorts.N = (Action<int>)ProvidedPorts.M); } }" =?
            "class X : Component { void M() {} extern void N(); void M(int i) {} extern void N(int i); X() { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(M)))); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__(int i);}"

    [<Test>]
    let ``normalizes disambiguated binding with many superfluous parantheses`` () =
        normalize "class X : Component { void M() {} extern void N(); void M(int i) {} extern void N(int i); X(X x) { BindDelayed(((((x).RequiredPorts).N) = ((Action<int>)(ProvidedPorts).M))); } }" =?
            "class X : Component { void M() {} extern void N(); void M(int i) {} extern void N(int i); X(X x) { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)((x).N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(M)))); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__(int i);}"