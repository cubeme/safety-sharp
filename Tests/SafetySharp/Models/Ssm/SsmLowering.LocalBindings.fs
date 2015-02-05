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

namespace Models.Ssm.Lowering

open System
open System.Linq
open NUnit.Framework
open Mono.Cecil
open SafetySharp.Modeling
open SafetySharp.Models
open SafetySharp.Models.Ssm

[<TestFixture>]
module ``Local bindings`` =
    let private transform csharpCode = 
        let csharpCode = sprintf "%s class TestModel : Model { public TestModel() { SetRootComponents(new X()); } }" csharpCode
        let model = TestCompilation.CreateModel csharpCode
        model.FinalizeMetadata ()
        let root = CilToSsm.transformModel model |> SsmLowering.lowerLocalBindings
        root.Subs.[0]

    let private transformMethod methodDefinition= 
        let ssm = transform methodDefinition
        ssm.Methods.[0] |> SsmToCSharp.transform |> printfn "%s"
        ssm.Methods.[0]

    let private tmp = CilToSsm.freshLocal
    let private methodName = CilToSsm.makeUniqueMethodName
    let private synName name inheritanceLevel overloadIndex synIndex = SsmLowering.makeSynPortName (methodName name inheritanceLevel overloadIndex) synIndex

    [<Test>]
    let ``does not change required port invocation`` () =
        transform "class X : Component { extern void M(); void N() { M(); } }" =?
            {
                Name = "Root0@0"
                Fields = []
                Subs = []
                Faults = []
                Bindings = []
                Methods = 
                    [
                        {
                            Name = methodName "M" 2 0
                            Kind = ReqPort
                            Params = []
                            Locals = []
                            Return = VoidType
                            Body = NopStm
                        }
                        {
                            Name = methodName "N" 2 0
                            Kind = ProvPort
                            Params = []
                            Locals = []
                            Return = VoidType
                            Body = SeqStm [ExprStm (CallExpr (methodName "M" 2 0, [], [], VoidType, [])); RetStm None]
                        }
                    ]
            }

    [<Test>]
    let ``introduces binding for provided port invocation`` () =
        transform "class X : Component { void M() { } void N() { M(); } }" =?
            {
                Name = "Root0@0"
                Fields = []
                Subs = []
                Faults = []
                Bindings = 
                    [
                        { 
                            SourceComp = "Root0@0"
                            SourcePort = methodName "M" 2 0
                            TargetComp = "Root0@0"; 
                            TargetPort = synName "M" 2 0 0
                            Kind = Instantaneous 
                        }
                    ]
                Methods = 
                    [
                        {
                            Name = methodName "M" 2 0
                            Kind = ProvPort
                            Params = []
                            Locals = []
                            Return = VoidType
                            Body = RetStm None
                        }
                        {
                            Name = methodName "N" 2 0
                            Kind = ProvPort
                            Params = []
                            Locals = []
                            Return = VoidType
                            Body = SeqStm [ExprStm (CallExpr (synName "M" 2 0 0, [], [], VoidType, [])); RetStm None]
                        }
                        {
                            Name = synName "M" 2 0 0
                            Kind = ReqPort
                            Params = []
                            Locals = []
                            Return = VoidType
                            Body = NopStm
                        }
                    ]
            }

    [<Test>]
    let ``introduces binding for provided port invocation of subcomponent`` () =
        transform "class Y : Component { public void M() { } } class X : Component { Y y = new Y(); void N() { y.M(); } }" =?
            {
                Name = "Root0@0"
                Fields = []
                Subs = 
                    [
                        {
                            Name = "Root0@0.y@0"
                            Fields = []
                            Subs = []
                            Faults = []
                            Bindings = []
                            Methods = 
                                [
                                    {
                                        Name = methodName "M" 2 0
                                        Kind = ProvPort
                                        Params = []
                                        Locals = []
                                        Return = VoidType
                                        Body = RetStm None
                                    }
                                ]
                        }
                    ]
                Faults = []
                Bindings = 
                    [
                        { 
                            SourceComp = "Root0@0.y@0"
                            SourcePort = methodName "M" 2 0
                            TargetComp = "Root0@0"; 
                            TargetPort = synName "M" 2 0 0
                            Kind = Instantaneous 
                        }
                    ]
                Methods = 
                    [
                        {
                            Name = methodName "N" 2 0
                            Kind = ProvPort
                            Params = []
                            Locals = []
                            Return = VoidType
                            Body = SeqStm [ExprStm (CallExpr (synName "M" 2 0 0, [], [], VoidType, [])); RetStm None]
                        }
                        {
                            Name = synName "M" 2 0 0
                            Kind = ReqPort
                            Params = []
                            Locals = []
                            Return = VoidType
                            Body = NopStm
                        }
                    ]
            }

    [<Test>]
    let ``introduces multiple bindings for provided port invocations`` () =
        transform "class Y : Component { public void M() { N(); } void N() {} } class X : Component { Y y = new Y(); void Q() {} void N() { y.M(); Q(); Q(); } }" =?
            {
                Name = "Root0@0"
                Fields = []
                Subs = 
                    [
                        {
                            Name = "Root0@0.y@0"
                            Fields = []
                            Subs = []
                            Faults = []
                            Bindings =
                                [
                                    { 
                                        SourceComp = "Root0@0.y@0"
                                        SourcePort = methodName "N" 2 0
                                        TargetComp = "Root0@0.y@0" 
                                        TargetPort = synName "N" 2 0 0
                                        Kind = Instantaneous 
                                    }
                                ]
                            Methods = 
                                [
                                    {
                                        Name = methodName "M" 2 0
                                        Kind = ProvPort
                                        Params = []
                                        Locals = []
                                        Return = VoidType
                                        Body = SeqStm [ExprStm (CallExpr (synName "N" 2 0 0, [], [], VoidType, [])); RetStm None]
                                    }
                                    {
                                        Name = methodName "N" 2 0
                                        Kind = ProvPort
                                        Params = []
                                        Locals = []
                                        Return = VoidType
                                        Body = RetStm None
                                    }
                                    {
                                        Name = synName "N" 2 0 0
                                        Kind = ReqPort
                                        Params = []
                                        Locals = []
                                        Return = VoidType
                                        Body = NopStm
                                    }
                                ]
                        }
                    ]
                Faults = []
                Bindings = 
                    [
                        { 
                            SourceComp = "Root0@0.y@0"
                            SourcePort = methodName "M" 2 0
                            TargetComp = "Root0@0"; 
                            TargetPort = synName "M" 2 0 0
                            Kind = Instantaneous 
                        }
                        { 
                            SourceComp = "Root0@0"
                            SourcePort = methodName "Q" 2 0
                            TargetComp = "Root0@0"; 
                            TargetPort = synName "Q" 2 0 1
                            Kind = Instantaneous 
                        }
                        { 
                            SourceComp = "Root0@0"
                            SourcePort = methodName "Q" 2 0
                            TargetComp = "Root0@0"; 
                            TargetPort = synName "Q" 2 0 2
                            Kind = Instantaneous 
                        }
                    ]
                Methods = 
                    [
                        {
                            Name = methodName "Q" 2 0
                            Kind = ProvPort
                            Params = []
                            Locals = []
                            Return = VoidType
                            Body = RetStm None
                        }
                        {
                            Name = methodName "N" 2 0
                            Kind = ProvPort
                            Params = []
                            Locals = []
                            Return = VoidType
                            Body = 
                                SeqStm [
                                    ExprStm (CallExpr (synName "M" 2 0 0, [], [], VoidType, []))
                                    ExprStm (CallExpr (synName "Q" 2 0 1, [], [], VoidType, []))
                                    ExprStm (CallExpr (synName "Q" 2 0 2, [], [], VoidType, []))
                                    RetStm None
                                ]
                        }
                        {
                            Name = synName "M" 2 0 0
                            Kind = ReqPort
                            Params = []
                            Locals = []
                            Return = VoidType
                            Body = NopStm
                        }
                        {
                            Name = synName "Q" 2 0 1
                            Kind = ReqPort
                            Params = []
                            Locals = []
                            Return = VoidType
                            Body = NopStm
                        }
                        {
                            Name = synName "Q" 2 0 2
                            Kind = ReqPort
                            Params = []
                            Locals = []
                            Return = VoidType
                            Body = NopStm
                        }
                    ]
            }