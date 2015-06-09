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
open SafetySharp.Compiler.Roslyn.Syntax
open SafetySharp.Compiler.Roslyn.Symbols

[<TestFixture; Ignore("Currently not working")>]
module BindingNormalizer =
    let normalize csharpCode = 
        TestCompilation.GetNormalizedClass (BindingNormalizer ()) csharpCode 

    [<Test>]
    let ``normalizes binding of ports of field subcomponent`` () =
        normalize "partial class X : Component { X x; void M() {} extern void N(); X() { Bind(x.RequiredPorts.N = x.ProvidedPorts.M).Delayed(); } }" =?
            ["class X : Component { X x; void M() {} extern void N(); X() { Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.M)))).Delayed(); } }";
            "[System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"]

    [<Test>]
    let ``normalizes binding of ports of parameter subcomponent`` () =
        normalize "partial class X : Component { void M(ref int i) {} extern void N(ref int i); X(X x, X y) { Bind(x.RequiredPorts.N = y.ProvidedPorts.M).Delayed(); } }" =?
            ["class X : Component { void M(ref int i) {} extern void N(ref int i); X(X x, X y) { Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(y.M)))).Delayed(); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__(ref int i);}"]

    [<Test>]
    let ``normalizes binding of ports of local variable subcomponent`` () =
        normalize "partial class X : Component { void M() {} extern void N(); X() { X x = null; Bind(x.RequiredPorts.N = x.ProvidedPorts.M).Delayed(); } }" =?
            ["class X : Component { void M() {} extern void N(); X() { X x = null; Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.M)))).Delayed(); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"]

    [<Test>]
    let ``normalizes binding of ports of property subcomponent`` () =
        normalize "partial class X : Component { X x { get; set; } void M() {} extern void N(); X() { Bind(x.RequiredPorts.N = x.ProvidedPorts.M).Delayed(); } }" =?
            ["class X : Component { X x { get; set; } void M() {} extern void N(); X() { Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.M)))).Delayed(); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"]

    [<Test>]
    let ``normalizes binding of ports of method returned subcomponent`` () =
        normalize "partial class X : Component { X x() { return null; } void M() {} extern void N(); X() { Bind(x().RequiredPorts.N = x().ProvidedPorts.M).Delayed(); } }" =?
            ["class X : Component { X x() { return null; } void M() {} extern void N(); X() { Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x().N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x().M)))).Delayed(); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"]

    [<Test>]
    let ``normalizes binding of ports of nested subcomponents`` () =
        normalize "interface I : IComponent { [Provided] void M(); [Required] void N(); } partial class X : Component { I i; X x() { return null; } X() { Bind(x().i.RequiredPorts.N = x().i.ProvidedPorts.M).Delayed(); } }" =?
            ["class X : Component { I i; X x() { return null; } X() { Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x().i.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x().i.M)))).Delayed(); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"]

    [<Test>]
    let ``normalizes binding of self-declared ports`` () =
        normalize "partial class X : Component { void M() {} extern void N(); X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); } }" =?
            ["class X : Component { void M() {} extern void N(); X() { Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(M)))).Delayed(); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"]

        normalize "partial class X : Component { void M() {} extern void N(); X() { Bind(RequiredPorts.N = ProvidedPorts.M); } }" =?
            ["class X : Component { void M() {} extern void N(); X() { Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(M)))); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"]

    [<Test>]
    let ``normalizes multiple bindings in same constructor`` () =
        normalize "partial class X : Component { void M() {} int P() { return 1; } extern void N(); extern int Q(); X(X x, X y) { Bind(x.RequiredPorts.N = y.ProvidedPorts.M); Bind(x.RequiredPorts.Q = y.ProvidedPorts.P).Delayed(); } }" =?
            ["class X : Component { void M() {} int P() { return 1; } extern void N(); extern int Q(); X(X x, X y) { Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(y.M)))); \
            Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate1__)(x.Q)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate1__)(y.P)))).Delayed(); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();\
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate int __BindingDelegate1__();}"]

    [<Test>]
    let ``normalizes multiple bindings in different constructors`` () =
        normalize "partial class X : Component { void M() {} int P() { return 1; } extern void N(); extern int Q(); X(X x, X y) { Bind(x.RequiredPorts.N = y.ProvidedPorts.M); } X(X x) { Bind(x.RequiredPorts.Q = x.ProvidedPorts.P).Delayed(); } }" =?
            ["class X : Component { void M() {} int P() { return 1; } extern void N(); extern int Q(); X(X x, X y) { Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(y.M)))); } \
            X(X x) { Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate1__)(x.Q)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate1__)(x.P)))).Delayed(); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();\
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate int __BindingDelegate1__();}"]

    [<Test>]
    let ``normalizes disambiguated binding`` () =
        normalize "partial class X : Component { void M() {} extern void N(); void M(int i) {} extern void N(int i); X() { Bind(RequiredPorts.N = (Action<int>)ProvidedPorts.M).Delayed(); } }" =?
            ["class X : Component { void M() {} extern void N(); void M(int i) {} extern void N(int i); X() { Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(M)))).Delayed(); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__(int i);}"]

    [<Test>]
    let ``normalizes disambiguated binding with many superfluous parantheses`` () =
        normalize "partial class X : Component { void M() {} extern void N(); void M(int i) {} extern void N(int i); X(X x) { Bind(((((x).RequiredPorts).N) = ((Action<int>)(ProvidedPorts).M))).Delayed(); } }" =?
            ["class X : Component { void M() {} extern void N(); void M(int i) {} extern void N(int i); X(X x) { Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)((x).N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(M)))).Delayed(); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__(int i);}"]

    [<Test>]
    let ``normalizes model binding in model-derived class`` () =
        normalize "partial class M : Model { class X : Component { public void M() {} public extern void N(); } M(X x1, X x2) { Bind(x1.RequiredPorts.N = x2.ProvidedPorts.M).Delayed(); } }" =?
            ["class M : Model { class X : Component { public void M() {} public extern void N(); } M(X x1, X x2) { Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x1.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x2.M)))).Delayed(); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"]

    [<Test>]
    let ``normalizes model binding in function using model class externally class`` () =
        normalize "partial class M { class X : Component { public void M() {} public extern void N(); } void Q(X x1, X x2, Model m) { m.Bind(x1.RequiredPorts.N = x2.ProvidedPorts.M).Delayed(); } }" =?
            ["class M { class X : Component { public void M() {} public extern void N(); } void Q(X x1, X x2, Model m) { m.Bind(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x1.N)), \
            SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(x2.M)))).Delayed(); } \
            [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();}"]

    [<Test>]
    let ``normalizes overridden provided port`` () =
        normalize "partial class Y : X { extern void N(); public override void M() {} Y() { Bind(RequiredPorts.N = ProvidedPorts.M); }} class X : Component { public virtual void M() {}}" =?
            ["class Y : X { extern void N(); public override void M() {} Y() { Bind(new SafetySharp.Modeling.PortBinding(\
             SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(N)), \
             SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(M)))); }\
             [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();} "]

    [<Test>]
    let ``normalizes overridden required port`` () =
        normalize "partial class Y : X { void N() {} public extern override void M(); Y() { Bind(RequiredPorts.M = ProvidedPorts.N); }} class X : Component { public virtual extern void M(); }" =?
            ["class Y : X { void N() {} public extern override void M(); Y() { Bind(new SafetySharp.Modeling.PortBinding(\
             SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(M)), \
             SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(N)))); }\
             [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();} "]

    [<Test>]
    let ``normalizes provided port replaced by new required port`` () =
        normalize "partial class Y : X { void N() {} public extern new void M(); Y() { Bind(RequiredPorts.M = ProvidedPorts.N); }} class X : Component { public void M() {}}" =?
            ["class Y : X { void N() {} public extern new void M(); Y() { Bind(new SafetySharp.Modeling.PortBinding(\
             SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(M)), \
             SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(N)))); }\
             [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();} "]

    [<Test>]
    let ``normalizes required port replaced by new provided port`` () =
        normalize "partial class Y : X { extern void N(); public new void M() {} Y() { Bind(RequiredPorts.N = ProvidedPorts.M); }} class X : Component { public extern void M(); }" =?
            ["class Y : X { extern void N(); public new void M() {} Y() { Bind(new SafetySharp.Modeling.PortBinding(\
             SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(N)), \
             SafetySharp.Modeling.PortInfo.MethodPort((__BindingDelegate0__)(M)))); }\
             [System.Runtime.CompilerServices.CompilerGeneratedAttribute()] private delegate void __BindingDelegate0__();} "]
