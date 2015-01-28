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

namespace Ssm

open System
open System.Linq
open NUnit.Framework
open Mono.Cecil
open SafetySharp.Modeling
open SafetySharp.Models
open SafetySharp.Models.Ssm

[<TestFixture>]
module ``Ssm Lowering of Port Signatures`` =
    let private className = "X"

    let private transform methodDefinition= 
        let csharpCode = sprintf "class %s : Component { %s } class TestModel : Model { public TestModel() { SetRootComponents(new X()); } }" className methodDefinition
        let model = TestCompilation.CreateModel csharpCode
        model.FinalizeMetadata ()
        let ssm = CilToSsm.transformModel model
        ssm.[0] |> SsmLowering.lowerSignatures

    let private transformMethod methodDefinition= 
        let ssm = transform methodDefinition
        ssm.Methods.[0] |> SsmToCSharp.transform |> printfn "%s"
        ssm.Methods.[0]

    let private tmp = CilToSsm.freshLocal
    let private methodId name = { Name = CilToSsm.makeUniqueMethodName name 2 0; Type = className }
    let private this = Some (VarExpr (This (ClassType className)))

    [<Test>]
    let ``does not change void-returning method`` () =
        transformMethod "void M() { return; }" =?
            {
                Name = CilToSsm.makeUniqueMethodName "M" 2 0
                Return = VoidType
                Params = []
                Locals = []
                Body = RetStm None
                Kind = ProvPort                   
            }

    [<Test>]
    let ``lowers value-returning method without parameters`` () =
        transformMethod "int M() { return M(); }" =?
            {
                Name = CilToSsm.makeUniqueMethodName "M" 2 0
                Return = VoidType
                Params = [ { Var = Arg ("retVal", IntType); Direction = Out } ]
                Locals = [tmp 1 0 IntType]
                Body = 
                    SeqStm 
                        [
                            CallStm (methodId "M", [IntType], [Out], VoidType, [VarRefExpr (tmp 1 0 IntType)], this)
                            SeqStm [
                                AsgnStm (Arg ("retVal", IntType), VarExpr (tmp 1 0 IntType))
                                RetStm None
                            ]
                        ]
                Kind = ProvPort                   
            }

    [<Test>]
    let ``does not change void-returning required port method`` () =
        transformMethod "extern void M();" =?
            {
                Name = CilToSsm.makeUniqueMethodName "M" 2 0
                Return = VoidType
                Params = []
                Locals = []
                Body = NopStm
                Kind = ReqPort                   
            }

    [<Test>]
    let ``lowers value-returning required port method without parameters`` () =
        transformMethod "extern int M();" =?
            {
                Name = CilToSsm.makeUniqueMethodName "M" 2 0
                Return = VoidType
                Params = [ { Var = Arg ("retVal", IntType); Direction = Out } ]
                Locals = []
                Body = NopStm
                Kind = ReqPort                   
            }

    [<Test>]
    let ``lowers value-returning required port method with parameters`` () =
        transformMethod "extern bool M(int x, ref bool b);" =?
            {
                Name = CilToSsm.makeUniqueMethodName "M" 2 0
                Return = VoidType
                Params =
                    [ 
                        { Var = Arg ("x", IntType); Direction = In }
                        { Var = Arg ("b", BoolType); Direction = InOut }
                        { Var = Arg ("retVal", BoolType); Direction = Out }
                    ]
                Locals = []
                Body = NopStm
                Kind = ReqPort                   
            }

    [<Test>]
    let ``lowers value-returning required port method with conflicting parameter`` () =
        transformMethod "extern int M(int retVal);" =?
            {
                Name = CilToSsm.makeUniqueMethodName "M" 2 0
                Return = VoidType
                Params = [ { Var = Arg ("retVal", IntType); Direction = In }; { Var = Arg ("retVal_", IntType); Direction = Out } ]
                Locals = []
                Body = NopStm
                Kind = ReqPort                   
            }

    [<Test>]
    let ``lowers value-returning method with conflicting parameter`` () =
        transformMethod "int M(int retVal) { return retVal; }" =?
            {
                Name = CilToSsm.makeUniqueMethodName "M" 2 0
                Return = VoidType
                Params = [ { Var = Arg ("retVal", IntType); Direction = In }; { Var = Arg ("retVal_", IntType); Direction = Out } ]
                Locals = []
                Body = 
                    SeqStm 
                        [
                            AsgnStm (Arg ("retVal_", IntType), VarExpr (Arg ("retVal", IntType)))
                            RetStm None
                        ]
                Kind = ProvPort                   
            }

    [<Test>]
    let ``lowers value-returning method with parameters`` () =
        transformMethod "bool M(int x, ref bool b) { return b || M(x, ref b); }" =?
            {
                Name = CilToSsm.makeUniqueMethodName "M" 2 0
                Return = VoidType
                Params =
                    [ 
                        { Var = Arg ("x", IntType); Direction = In }
                        { Var = Arg ("b", BoolType); Direction = InOut }
                        { Var = Arg ("retVal", BoolType); Direction = Out }
                    ]
                Locals = [tmp 6 0 BoolType]
                Body = 
                    IfStm (
                        VarExpr (Arg ("b", BoolType)),
                        SeqStm [AsgnStm (Arg ("retVal", BoolType), BoolExpr true); RetStm None],
                        SeqStm [
                            CallStm (methodId "M", [IntType; BoolType; BoolType], [In; InOut; Out], VoidType, [VarExpr (Arg ("x", IntType)); VarRefExpr (Arg ("b", BoolType)); VarRefExpr (tmp 6 0 BoolType)], this)
                            SeqStm [
                                AsgnStm (Arg ("retVal", BoolType), VarExpr (tmp 6 0 BoolType))
                                RetStm None
                            ] 
                        ]
                    )
                Kind = ProvPort                   
            }

    [<Test>]
    let ``lowers subcomponents`` () =
        transform "int M() { return q.Q(); } Sub q = new Sub(); class Sub : Component { public extern int Q(); } " =?
            {
                Name = "Root0"
                Fields = []
                Methods = 
                    [
                       {
                            Name = CilToSsm.makeUniqueMethodName "M" 2 0
                            Return = VoidType
                            Params = [ { Var = Arg ("retVal", IntType); Direction = Out } ]
                            Locals = [tmp 2 0 IntType]
                            Body = 
                                SeqStm 
                                    [
                                        CallStm ({ Type = "X.Sub"; Name = CilToSsm.makeUniqueMethodName "Q" 2 0 }, [IntType], [Out], VoidType, [VarRefExpr (tmp 2 0 IntType)], Some (VarExpr (Field (CilToSsm.makeUniqueFieldName "q" 2, ClassType "X.Sub"))))
                                        SeqStm [
                                            AsgnStm (Arg ("retVal", IntType), VarExpr (tmp 2 0 IntType))
                                            RetStm None
                                        ]
                                    ]
                            Kind = ProvPort         
                        }
                    ]
                Subs = 
                    [
                        {
                            Name = "Root0.q@0"
                            Fields = []
                            Subs = []
                            Methods = 
                                [
                                    {
                                        Name = CilToSsm.makeUniqueMethodName "Q" 2 0
                                        Return = VoidType
                                        Params = [ { Var = Arg ("retVal", IntType); Direction = Out } ]
                                        Locals = []
                                        Body = NopStm
                                        Kind = ReqPort                   
                                    }
                                ]
                        }
                    ]          
            }