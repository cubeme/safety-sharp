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
open SafetySharp.Tests

[<TestFixture>]
module ``Ssm Lowering to Single Exit Point`` =
    let private className = "X"

    let private transform methodDefinition= 
        let csharpCode = sprintf "class %s : Component { %s } class TestModel : Model { public TestModel() { SetRootComponents(new X()); } }" className methodDefinition
        let model = createModel csharpCode
        model.FinalizeMetadata ()
        let ssm = CilToSsm.transformModel model
        ssm.[0] |> SsmLowering.lowerSignatures |> SsmLowering.lowerExitPoints

    let private transformMethod methodDefinition= 
        let ssm = transform methodDefinition
        ssm.Methods.[0] |> SsmToCSharp.transform |> printfn "%s"
        ssm.Methods.[0]

    let private tmp = CilToSsm.freshLocal
    let private methodId name = { Name = CilToSsm.makeUniqueMethodName name 2 0; Type = className }
    let private this = Some (VarExpr (This (ClassType className)))

    [<Test>]
    let ``does not change required port method`` () =
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
    let ``does not change empty method with single exit point`` () =
        transformMethod "void M() {}" =?
            {
                Name = CilToSsm.makeUniqueMethodName "M" 2 0
                Return = VoidType
                Params = []
                Locals = []
                Body = NopStm
                Kind = ProvPort                   
            }

    [<Test>]
    let ``does not change non-empty method with single exit point`` () =
        transformMethod "int _f; void M() {  if (_f > 0) _f = 1; }" =?
            {
                Name = CilToSsm.makeUniqueMethodName "M" 2 0
                Return = VoidType
                Params = []
                Locals = []
                Body = SeqStm [
                        IfStm (
                            BExpr (VarExpr (Field ("_f", IntType)), Gt, IntExpr 0),
                            AsgnStm (Field ("_f", IntType), IntExpr 1), 
                            NopStm)
                        NopStm
                    ]
                Kind = ProvPort                   
            }