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
open SafetySharp.Runtime.Modeling
open SafetySharp.Models
open SafetySharp.Models.Ssm

[<TestFixture>]
module ``Step inlining`` =
    let private transform csharpCode = 
        let csharpCode = sprintf "%s class TestModel : Model { public TestModel() { SetRootComponents(new X()); } }" csharpCode
        let model = TestCompilation.CreateModel csharpCode
        model.FinalizeMetadata ()
        let metadataProvider = model.GetMetadataProvider ()
        let root = CilToSsm.transformModel model |> SsmLowering.lowerVirtualCalls model metadataProvider |> SsmLowering.lowerBaseSteps
        let c = root.Subs.[0]
        let steps = c.Methods |> List.filter (fun m -> m.Kind = Step)
        steps.Length =? 1
        steps.[0].Body

    let private tmp level pc idx t = 
        let tmp = CilToSsm.freshLocal pc idx t
        Local ((methodName "Update" level 0) + "!@!" + (Ssm.getVarName tmp), Ssm.getVarType tmp)

    [<Test>]
    let ``contains empty update method`` () =
        transform "class X : Component {}" =? NopStm

    [<Test>]
    let ``does not change Update method without base call`` () =
        transform "class X : Component { int x; public override void Update() { x = 0; } }" =? 
            SeqStm [AsgnStm (Field (fieldName "x" 2, IntType), IntExpr 0); NopStm]

    [<Test>]
    let ``inlines base call with conflicting local variables`` () =
        transform 
            "class Y : Component { protected int R() { return 1; } protected int x; public override void Update() { x = R(); } }
             class X : Y { public override void Update() { x = R() + 1; base.Update(); }} 
            " =? SeqStm [
                    AsgnStm (tmp 3 2 0 IntType, CallExpr (methodName "R" 2 0, "Y", [], [], IntType, [], false))
                    AsgnStm (Field (fieldName "x" 2, IntType), BExpr (VarExpr (tmp 3 2 0 IntType), Add, IntExpr 1))
                    SeqStm [
                        AsgnStm (tmp 2 2 0 IntType, CallExpr (methodName "R" 2 0, "Y", [], [], IntType, [], false))
                        AsgnStm (Field (fieldName "x" 2, IntType), VarExpr (tmp 2 2 0 IntType))
                        NopStm
                    ]
                    NopStm
                 ]