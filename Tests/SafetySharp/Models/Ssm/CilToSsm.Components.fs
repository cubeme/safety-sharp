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

namespace Models.Ssm.CilToSsm

open System
open System.Linq
open NUnit.Framework
open Mono.Cecil
open SafetySharp.Modeling
open SafetySharp.Models
open SafetySharp.Models.Ssm

[<TestFixture>]
module Components =
    let private transform csharpCode instantiations =
        let compilation = TestCompilation (sprintf "class T : Model { public T() { AddRootComponents(%s); } } %s" instantiations csharpCode)
        let assembly = compilation.CompileSSharp (false)
        let modelType = assembly.GetType "T"
        let model = Activator.CreateInstance modelType :?> Model
        model.FinalizeMetadata ()
        let root = CilToSsm.transformModel model
        root.Subs

    [<Test; Ignore>]
    let ``transform subcomponents of derived component with non-conflicting names`` () =
        transform "class S : Component {} class X : Component { S s = new S(); } class Y : X { S s1 = new S(); S s2 = new S(); }" "new Y()" =?
            [
                {
                    Name = "R.Y0@0"
                    Fields = []
                    Methods = [Ssm.BaseUpdateMethod]
                    Subs =
                        [
                            {
                                Name = "R.Y0@0.s@0"
                                Fields = []
                                Methods = [Ssm.BaseUpdateMethod]
                                Subs = []
                                Faults = []
                                Bindings = []
                            }
                            {
                                Name = "R.Y0@0.s1@1"
                                Fields = []
                                Methods = [Ssm.BaseUpdateMethod]
                                Subs = []
                                Faults = []
                                Bindings = []
                            }
                            {
                                Name = "R.Y0@0.s2@2"
                                Fields = []
                                Methods = [Ssm.BaseUpdateMethod]
                                Subs = []
                                Faults = []
                                Bindings = []
                            }
                        ]
                    Faults = []
                    Bindings = []
                }
            ]

    [<Test; Ignore>]
    let ``transform subcomponents of derived component with conflicting names`` () =
        transform "class S : Component {} class X : Component { S s = new S(); } class Y : X { S s = new S(); S s2 = new S(); }" "new Y()" =?
            [
                {
                    Name = "R.Y0@0"
                    Fields = []
                    Methods = [Ssm.BaseUpdateMethod]
                    Subs =
                        [
                            {
                                Name = "R.Y0@0.s@0"
                                Fields = []
                                Methods = [Ssm.BaseUpdateMethod]
                                Subs = []
                                Faults = []
                                Bindings = []
                            }
                            {
                                Name = "R.Y0@0.s@1"
                                Fields = []
                                Methods = [Ssm.BaseUpdateMethod]
                                Subs = []
                                Faults = []
                                Bindings = []
                            }
                            {
                                Name = "R.Y0@0.s2@2"
                                Fields = []
                                Methods = [Ssm.BaseUpdateMethod]
                                Subs = []
                                Faults = []
                                Bindings = []
                            }
                        ]
                    Faults = []
                    Bindings = []
                }
            ]

    [<Test>]
    let ``transform component without simple method`` () =
        transform "namespace Y { class X : Component { int M() { return 1; }}}" "new Y.X()" =?
        [
            {
                Name = "R.X0@0"
                Fields = []
                Subs = []
                Methods = 
                    [
                        Ssm.BaseUpdateMethod
                        {
                            Name = methodName "M" 2 0
                            Return = IntType
                            Params = []
                            Locals = []
                            Body = RetStm (Some (IntExpr 1))
                            Kind = ProvPort
                        }
                    ]
                Faults = []
                Bindings = []
            }
        ]

    [<Test>]
    let ``transform component with subcomponent`` () =
        transform "class X : Component { public void M() {} } class Y : Component { X x = new X(); void N() { x.M(); }}" "new Y()" =?
        [
            {
                Name = "R.Y0@0"
                Fields = []
                Subs = 
                    [
                        {
                            Name = "R.Y0@0.x@0"
                            Fields = []
                            Subs = []
                            Methods = 
                                [
                                    Ssm.BaseUpdateMethod
                                    {
                                        Name = methodName "M" 2 0
                                        Return = VoidType
                                        Params = []
                                        Locals = []
                                        Body = RetStm None
                                        Kind = ProvPort
                                    } 
                                ]
                            Faults = []
                            Bindings = []
                        } 
                    ]
                Methods = 
                    [
                        Ssm.BaseUpdateMethod
                        {
                            Name = methodName "N" 2 0
                            Return = VoidType
                            Params = []
                            Locals = []
                            Body = SeqStm 
                                [
                                    ExprStm (MemberExpr (Field ("R.Y0@0.x@0", ClassType "X"),
                                                         CallExpr (methodName "M" 2 0, "X", [], [], VoidType, [], true)))
                                    RetStm None
                                ]
                            Kind = ProvPort
                        } 
                    ]
                Faults = []
                Bindings = []
            }
        ]