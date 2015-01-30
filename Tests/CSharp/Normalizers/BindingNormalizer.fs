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
    let normalize = 
        TestCompilation.GetNormalizedClass (BindingNormalizer ())

    [<Test>]
    let ``normalizes unambiguous binding of ports of field subcomponent`` () =
        normalize "class X : Component { X x; void M() {} extern void N(); X() { BindDelayed(x.RequiredPorts.N = x.ProvidedPorts.M); } }" =?
            "class X : Component { X x; void M() {} extern void N(); X() { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.RequiredPort((X.__N____Delegate__)(x.N), \"__N____Field__\"), \
            SafetySharp.Modeling.PortInfo.ProvidedPort((X.__M____Delegate__)(x.M)))); } }"

    [<Test>]
    let ``normalizes unambiguous binding of ports of parameter subcomponent`` () =
        normalize "class X : Component { void M() {} extern void N(); X(X x, X y) { BindDelayed(x.RequiredPorts.N = y.ProvidedPorts.M); } }" =?
            "class X : Component { void M() {} extern void N(); X(X x, X y) { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.RequiredPort((X.__N____Delegate__)(x.N), \"__N____Field__\"), \
            SafetySharp.Modeling.PortInfo.ProvidedPort((X.__M____Delegate__)(y.M)))); } }"

    [<Test>]
    let ``normalizes unambiguous binding of ports of local variable subcomponent`` () =
        normalize "class X : Component { void M() {} extern void N(); X() { X x = null; BindDelayed(x.RequiredPorts.N = x.ProvidedPorts.M); } }" =?
            "class X : Component { void M() {} extern void N(); X() { X x = null; BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.RequiredPort((X.__N____Delegate__)(x.N), \"__N____Field__\"), \
            SafetySharp.Modeling.PortInfo.ProvidedPort((X.__M____Delegate__)(x.M)))); } }"

    [<Test>]
    let ``normalizes unambiguous binding of ports of property subcomponent`` () =
        normalize "class X : Component { X x { get; set; } void M() {} extern void N(); X() { BindDelayed(x.RequiredPorts.N = x.ProvidedPorts.M); } }" =?
            "class X : Component { X x { get; set; } void M() {} extern void N(); X() { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.RequiredPort((X.__N____Delegate__)(x.N), \"__N____Field__\"), \
            SafetySharp.Modeling.PortInfo.ProvidedPort((X.__M____Delegate__)(x.M)))); } }"

    [<Test>]
    let ``normalizes unambiguous binding of ports of method returned subcomponent`` () =
        normalize "class X : Component { X x() { return null; } void M() {} extern void N(); X() { BindDelayed(x().RequiredPorts.N = x().ProvidedPorts.M); } }" =?
            "class X : Component { X x() { return null; } void M() {} extern void N(); X() { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.RequiredPort((X.__N____Delegate__)(x().N), \"__N____Field__\"), \
            SafetySharp.Modeling.PortInfo.ProvidedPort((X.__M____Delegate__)(x().M)))); } }"

    [<Test>]
    let ``normalizes unambiguous binding of ports of nested subcomponents`` () =
        normalize "interface I : IComponent { [Provided] void M(); [Required] void N(); } class X : Component { I i; X x() { return null; } X() { BindDelayed(x().i.RequiredPorts.N = x().i.ProvidedPorts.M); } }" =?
            "class X : Component { I i; X x() { return null; } X() { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.RequiredPort((I.__N____Delegate__)(x().i.N), \"__N____Field__\"), \
            SafetySharp.Modeling.PortInfo.ProvidedPort((I.__M____Delegate__)(x().i.M)))); } }"

    [<Test>]
    let ``normalizes unambiguous binding of self-declared ports`` () =
        normalize "class X : Component { void M() {} extern void N(); X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); } }" =?
            "class X : Component { void M() {} extern void N(); X() { BindDelayed(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.RequiredPort((X.__N____Delegate__)(N), \"__N____Field__\"), \
            SafetySharp.Modeling.PortInfo.ProvidedPort((X.__M____Delegate__)(M)))); } }"

        normalize "class X : Component { void M() {} extern void N(); X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); } }" =?
            "class X : Component { void M() {} extern void N(); X() { BindInstantaneous(new SafetySharp.Modeling.PortBinding\
            (SafetySharp.Modeling.PortInfo.RequiredPort((X.__N____Delegate__)(N), \"__N____Field__\"), \
            SafetySharp.Modeling.PortInfo.ProvidedPort((X.__M____Delegate__)(M)))); } }"