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
module ProvidedPortNormalizer =
    let normalize csharpCode = 
        TestCompilation.GetNormalizedClass (ProvidedPortNormalizer()) (sprintf "using System.Diagnostics; %s" csharpCode)

    [<Test>]
    let ``does not normalize method not declared within a component class`` () =
        normalize "class X { void M() {} }" =? "class X { void M() {} }"

    [<Test>]
    let ``does not normalize extern component method`` () =
        normalize "class X : Component { extern void M(); }" =? "class X : Component { extern void M(); }"

    [<Test>]
    let ``does not normalize component method that is already marked with the attribute`` () =
        normalize "class X : Component { [Provided] void M() {} }" =? "class X : Component { [Provided] void M() {} }"

    [<Test>]
    let ``normalizes provided port of component`` () =
        normalize "class X : Component { void M() {} }" =?
            "class X : Component { [SafetySharp.Modeling.ProvidedAttribute()] void M() {} }"
        normalize "class X : Component { protected void M() {} }" =? 
            "class X : Component { [SafetySharp.Modeling.ProvidedAttribute()] protected void M() {} }"

    [<Test>]
    let ``normalizes implicitly implemented provided port of component`` () =
        normalize "namespace Q { interface I { void M(); }} class X : Component, Q.I { void Q.I.M() {} }" =? 
            "class X : Component, Q.I { [SafetySharp.Modeling.ProvidedAttribute()] void Q.I.M() {} }"

    [<Test>]
    let ``normalizes multiple provided ports of component`` () =
        normalize "class X : Component { void M() {} void N() {} }" =?
            "class X : Component { [SafetySharp.Modeling.ProvidedAttribute()] void M() {} [SafetySharp.Modeling.ProvidedAttribute()] void N() {} }"

    [<Test>]
    let ``normalizes provided port of component and keeps all attributes`` () =
        normalize "class X : Component { [DebuggerHidden] void M() {} }" =? 
            "class X : Component { [DebuggerHidden] [SafetySharp.Modeling.ProvidedAttribute()] void M() {} }"
        normalize "class X : Component { [DebuggerHidden, DebuggerNonUserCode] void M() {} }" =? 
            "class X : Component { [DebuggerHidden, DebuggerNonUserCode] [SafetySharp.Modeling.ProvidedAttribute()] void M() {} }"
        normalize "class X : Component { [DebuggerHidden] [DebuggerNonUserCode] void M() {} }" =? 
            "class X : Component { [DebuggerHidden] [DebuggerNonUserCode] [SafetySharp.Modeling.ProvidedAttribute()] void M() {} }"