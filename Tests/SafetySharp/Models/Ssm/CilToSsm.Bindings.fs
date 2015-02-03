﻿// The MIT License (MIT)
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

namespace Models.Ssm

open System
open System.Linq
open NUnit.Framework
open Mono.Cecil
open SafetySharp.Modeling
open SafetySharp.Models
open SafetySharp.Models.Ssm

[<TestFixture>]
module ``CilToSsm Bindings`` =
   
    let private transform componentCode initCode = 
        let model = TestCompilation.CreateModel (sprintf "%s class TestModel : Model { public TestModel() { SetRootComponents(%s); } }" componentCode initCode)
        model.FinalizeMetadata ()
        let ssm = CilToSsm.transformModel model
        ssm.[0].Bindings

    [<Test>]
    let ``component without bindings`` () =
        transform "class X : Component { extern void N(); void M() {} }" "new X()" =? []

    [<Test>]
    let ``component with single delayed binding`` () =
        transform "class X : Component { extern void N(); void M() {} public X() { BindDelayed(RequiredPorts.N = ProvidedPorts.M); } }" "new X()" =? 
            [
                { 
                    TargetComp =  "Root@0"
                    SourceComp = "Root@0"
                    TargetPort = CilToSsm.makeUniqueMethodName "N" 2 0
                    SourcePort = CilToSsm.makeUniqueMethodName "M" 2 0
                    Kind = BindingKind.Delayed
                }
            ]

    [<Test>]
    let ``component with single instantaneous binding`` () =
        transform "class X : Component { extern void N(); void M() {} public X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); } }" "new X()" =? 
            [
                { 
                    TargetComp =  "Root@0"
                    SourceComp = "Root@0"
                    TargetPort = CilToSsm.makeUniqueMethodName "N" 2 0
                    SourcePort = CilToSsm.makeUniqueMethodName "M" 2 0
                    Kind = BindingKind.Instantaneous
                }
            ]

    [<Test>]
    let ``component with multiple bindings`` () =
        transform "class X : Component { extern void N(); void M() {} extern int Q(int i); int P(int i) { return i; } public X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); BindDelayed(RequiredPorts.Q = ProvidedPorts.P); } }" "new X()" =? 
            [
                { 
                    TargetComp =  "Root@0"
                    SourceComp = "Root@0"
                    TargetPort = CilToSsm.makeUniqueMethodName "N" 2 0
                    SourcePort = CilToSsm.makeUniqueMethodName "M" 2 0
                    Kind = BindingKind.Instantaneous
                }
                { 
                    TargetComp =  "Root@0"
                    SourceComp = "Root@0"
                    TargetPort = CilToSsm.makeUniqueMethodName "Q" 2 0
                    SourcePort = CilToSsm.makeUniqueMethodName "P" 2 0
                    Kind = BindingKind.Delayed
                }
            ]

    [<Test>]
    let ``subcomponent as source`` () =
        transform "class Y : Component { public extern void N(); } class X : Component { Y y = new Y(); void M() {} public X() { BindDelayed(y.RequiredPorts.N = ProvidedPorts.M); } }" "new X()" =? 
            [
                { 
                    TargetComp =  "Root@0.y@0"
                    SourceComp = "Root@0"
                    TargetPort = CilToSsm.makeUniqueMethodName "N" 2 0
                    SourcePort = CilToSsm.makeUniqueMethodName "M" 2 0
                    Kind = BindingKind.Delayed
                }
            ]

    [<Test>]
    let ``subcomponent as target`` () =
        transform "class Y : Component { public void N() {} } class X : Component { Y y = new Y(); extern void M(); public X() { BindDelayed(RequiredPorts.M = y.ProvidedPorts.N); } }" "new X()" =? 
            [
                { 
                    TargetComp =  "Root@0"
                    SourceComp = "Root@0.y@0"
                    TargetPort = CilToSsm.makeUniqueMethodName "M" 2 0
                    SourcePort = CilToSsm.makeUniqueMethodName "N" 2 0
                    Kind = BindingKind.Delayed
                }
            ]

    [<Test>]
    let ``subcomponent as source and target`` () =
        transform "class Y : Component { public void N() {} public extern void M(); } class X : Component { Y y = new Y(); public X() { BindDelayed(y.RequiredPorts.M = y.ProvidedPorts.N); } }" "new X()" =? 
            [
                { 
                    TargetComp =  "Root@0.y@0"
                    SourceComp = "Root@0.y@0"
                    TargetPort = CilToSsm.makeUniqueMethodName "M" 2 0
                    SourcePort = CilToSsm.makeUniqueMethodName "N" 2 0
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
                            BindDelayed(RequiredPorts.Q = z.ProvidedPorts.N);
                            BindDelayed(z.RequiredPorts.M = z.ProvidedPorts.Q);
                        }
                   }
                   delegate void D(out int i);
                   class X : W { 
                        extern void Q(); 
                        extern void Q(out int i);
                        Y y = new Y();
                        
                        public X() { 
                            BindDelayed(RequiredPorts.Q = (D)y.ProvidedPorts.N); 
                        }
                   }" "new X()" =? 
            [
                { 
                    TargetComp =  "Root@0"
                    SourceComp = "Root@0.z@0"
                    TargetPort = CilToSsm.makeUniqueMethodName "Q" 2 0
                    SourcePort = CilToSsm.makeUniqueMethodName "N" 2 0
                    Kind = BindingKind.Delayed
                }
                { 
                    TargetComp =  "Root@0.z@0"
                    SourceComp = "Root@0.z@0"
                    TargetPort = CilToSsm.makeUniqueMethodName "M" 2 0
                    SourcePort = CilToSsm.makeUniqueMethodName "Q" 3 0
                    Kind = BindingKind.Delayed
                }
                { 
                    TargetComp =  "Root@0"
                    SourceComp = "Root@0.y@1"
                    TargetPort = CilToSsm.makeUniqueMethodName "Q" 3 1
                    SourcePort = CilToSsm.makeUniqueMethodName "N" 2 1
                    Kind = BindingKind.Delayed
                }
            ]

    [<Test>]
    let ``transforms cyclic bindings`` () =
        transform "class X : Component { extern void N(); void M() { N(); } public X() { BindInstantaneous(RequiredPorts.N = ProvidedPorts.M); } }" "new X()" =? 
            [
                { 
                    TargetComp =  "Root@0"
                    SourceComp = "Root@0"
                    TargetPort = CilToSsm.makeUniqueMethodName "N" 2 0
                    SourcePort = CilToSsm.makeUniqueMethodName "M" 2 0
                    Kind = BindingKind.Instantaneous
                }
            ]