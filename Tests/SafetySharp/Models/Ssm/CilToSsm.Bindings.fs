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

namespace Models.Ssm.CilToSsm

open System
open System.Linq
open NUnit.Framework
open Mono.Cecil
open SafetySharp.Modeling
open SafetySharp.Models
open SafetySharp.Models.Ssm

[<TestFixture>]
module Bindings =
   
    let private transform componentCode initCode = 
        let model = TestCompilation.CreateModel (sprintf "%s class TestModel : Model { public TestModel() { SetRootComponents(%s); } }" componentCode initCode)
        model.FinalizeMetadata ()
        let root = CilToSsm.transformModel model
        root.Subs.[0].Bindings

    [<Test>]
    let ``component without bindings`` () =
        transform "class X : Component { extern void N(); void M() {} }" "new X()" =? []

    [<Test>]
    let ``component with single delayed binding`` () =
        transform "class X : Component { extern void N(); void M() {} public X() { Bind(RequiredPorts.N = ProvidedPorts.M).Delayed(); } }" "new X()" =? 
            [
                { 
                    TargetComp =  "R.X0@0"
                    SourceComp = "R.X0@0"
                    TargetPort = methodName "N" 2 0
                    SourcePort = methodName "M" 2 0
                    Kind = BindingKind.Delayed
                }
            ]

    [<Test>]
    let ``component with single instantaneous binding`` () =
        transform "class X : Component { extern void N(); void M() {} public X() { Bind(RequiredPorts.N = ProvidedPorts.M); } }" "new X()" =? 
            [
                { 
                    TargetComp =  "R.X0@0"
                    SourceComp = "R.X0@0"
                    TargetPort = methodName "N" 2 0
                    SourcePort = methodName "M" 2 0
                    Kind = BindingKind.Instantaneous
                }
            ]

    [<Test>]
    let ``component with multiple bindings`` () =
        transform "class X : Component { extern void N(); void M() {} extern int Q(int i); int P(int i) { return i; } public X() { Bind(RequiredPorts.N = ProvidedPorts.M); Bind(RequiredPorts.Q = ProvidedPorts.P).Delayed(); } }" "new X()" =? 
            [
                { 
                    TargetComp =  "R.X0@0"
                    SourceComp = "R.X0@0"
                    TargetPort = methodName "N" 2 0
                    SourcePort = methodName "M" 2 0
                    Kind = BindingKind.Instantaneous
                }
                { 
                    TargetComp =  "R.X0@0"
                    SourceComp = "R.X0@0"
                    TargetPort = methodName "Q" 2 0
                    SourcePort = methodName "P" 2 0
                    Kind = BindingKind.Delayed
                }
            ]

    [<Test>]
    let ``subcomponent as source`` () =
        transform "class Y : Component { public extern void N(); } class X : Component { Y y = new Y(); void M() {} public X() { Bind(y.RequiredPorts.N = ProvidedPorts.M).Delayed(); } }" "new X()" =? 
            [
                { 
                    TargetComp =  "R.X0@0.y@0"
                    SourceComp = "R.X0@0"
                    TargetPort = methodName "N" 2 0
                    SourcePort = methodName "M" 2 0
                    Kind = BindingKind.Delayed
                }
            ]

    [<Test>]
    let ``subcomponent as target`` () =
        transform "class Y : Component { public void N() {} } class X : Component { Y y = new Y(); extern void M(); public X() { Bind(RequiredPorts.M = y.ProvidedPorts.N).Delayed(); } }" "new X()" =? 
            [
                { 
                    TargetComp =  "R.X0@0"
                    SourceComp = "R.X0@0.y@0"
                    TargetPort = methodName "M" 2 0
                    SourcePort = methodName "N" 2 0
                    Kind = BindingKind.Delayed
                }
            ]

    [<Test>]
    let ``subcomponent as source and target`` () =
        transform "class Y : Component { public void N() {} public extern void M(); } class X : Component { Y y = new Y(); public X() { Bind(y.RequiredPorts.M = y.ProvidedPorts.N).Delayed(); } }" "new X()" =? 
            [
                { 
                    TargetComp =  "R.X0@0.y@0"
                    SourceComp = "R.X0@0.y@0"
                    TargetPort = methodName "M" 2 0
                    SourcePort = methodName "N" 2 0
                    Kind = BindingKind.Delayed
                }
            ]

    [<Test>]
    let ``multiple inherited and non-inherited bindings`` () =
        transform "class Y : Component { public void N() {} public void N(out int i) { i = 0; } public extern void M(); } 
                   class Z : Y { public void Q() {} } 
                   class W : Component {
                        Z z = new Z();
                        extern void Q();
                        
                        public W() {
                            Bind(RequiredPorts.Q = z.ProvidedPorts.N).Delayed();
                            Bind(z.RequiredPorts.M = z.ProvidedPorts.Q).Delayed();
                        }
                   }
                   delegate void D(out int i);
                   class X : W { 
                        extern void Q(); 
                        extern void Q(out int i);
                        Y y = new Y();
                        
                        public X() { 
                            Bind(RequiredPorts.Q = (D)y.ProvidedPorts.N).Delayed(); 
                        }
                   }" "new X()" =? 
            [
                { 
                    TargetComp =  "R.X0@0"
                    SourceComp = "R.X0@0.z@0"
                    TargetPort = methodName "Q" 2 0
                    SourcePort = methodName "N" 2 0
                    Kind = BindingKind.Delayed
                }
                { 
                    TargetComp =  "R.X0@0.z@0"
                    SourceComp = "R.X0@0.z@0"
                    TargetPort = methodName "M" 2 0
                    SourcePort = methodName "Q" 3 0
                    Kind = BindingKind.Delayed
                }
                { 
                    TargetComp =  "R.X0@0"
                    SourceComp = "R.X0@0.y@1"
                    TargetPort = methodName "Q" 3 1
                    SourcePort = methodName "N" 2 1
                    Kind = BindingKind.Delayed
                }
            ]

    [<Test>]
    let ``transforms cyclic bindings`` () =
        transform "class X : Component { extern void N(); void M() { N(); } public X() { Bind(RequiredPorts.N = ProvidedPorts.M); } }" "new X()" =? 
            [
                { 
                    TargetComp =  "R.X0@0"
                    SourceComp = "R.X0@0"
                    TargetPort = methodName "N" 2 0
                    SourcePort = methodName "M" 2 0
                    Kind = BindingKind.Instantaneous
                }
            ]

    [<Test>]
    let ``binding with virtual provided port`` () =
        transform "class Y : Component { public virtual void M() {} } class X : Y { public override void M() {} extern void N(); public X() { Bind(RequiredPorts.N = ProvidedPorts.M); } }" "new X()" =?
            [
                {
                    Kind = BindingKind.Instantaneous
                    SourceComp = "R.X0@0"
                    TargetComp = "R.X0@0"
                    TargetPort = methodName "N" 3 0
                    SourcePort = methodName "M" 3 0
                }
            ]

        transform "class Y : Component { public virtual void M() {} public extern void N(); } class Z : Y { public override void M() {} } class X : Component { Y y = new Z(); public X() { Bind(y.RequiredPorts.N = y.ProvidedPorts.M); } }" "new X()" =?
            [
                {
                    Kind = BindingKind.Instantaneous
                    SourceComp = "R.X0@0.y@0"
                    TargetComp = "R.X0@0.y@0"
                    TargetPort = methodName "N" 2 0
                    SourcePort = methodName "M" 3 0
                }
            ]

    [<Test>]
    let ``binding with interface provided port`` () =
        transform "interface I : IComponent { [Provided] void M(); } class Y : Component, I { public void M() {} } class X : Component { I y = new Y(); public extern void N(); public X() { Bind(RequiredPorts.N = y.ProvidedPorts.M); } }" "new X()" =?
            [
                {
                    Kind = BindingKind.Instantaneous
                    SourceComp = "R.X0@0.y@0"
                    TargetComp = "R.X0@0"
                    TargetPort = methodName "N" 2 0
                    SourcePort = methodName "M" 2 0
                }
            ]

        transform "interface I : IComponent { [Provided] void M(); } class Y : Component, I { public virtual void M() {} } class Z : Y { public override void M() {} } class X : Component { I i = new Z(); public extern void N(); public X() { Bind(RequiredPorts.N = i.ProvidedPorts.M); } }" "new X()" =?
            [
                {
                    Kind = BindingKind.Instantaneous
                    SourceComp = "R.X0@0.i@0"
                    TargetComp = "R.X0@0"
                    TargetPort = methodName "N" 2 0
                    SourcePort = methodName "M" 3 0
                }
            ]

        transform "interface I : IComponent { [Provided] void M(); } class Y : Component, I { void I.M() {} } class X : Component { I y = new Y(); public extern void N(); public X() { Bind(RequiredPorts.N = y.ProvidedPorts.M); } }" "new X()" =?
            [
                {
                    Kind = BindingKind.Instantaneous
                    SourceComp = "R.X0@0.y@0"
                    TargetComp = "R.X0@0"
                    TargetPort = methodName "N" 2 0
                    SourcePort = methodName "I.M" 2 0
                }
            ]