// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineeringgineering
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

namespace Transformations

open System
open NUnit.Framework
open SafetySharp.Models
open SafetySharp.Modeling

[<TestFixture>]
module ``SsmToScm Transformation`` =
    
    let private ssmComp : Ssm.Comp = {
        Name = "X"
        Subs = []
        Fields = []
        Methods = []
        Faults = []
        Bindings = []
    }

    let private scmComp : Scm.CompDecl = {
        Comp = Scm.Comp "X"
        Subs = []
        Fields = []
        ProvPorts = []
        ReqPorts = []
        Steps = []
        Faults = []
        Bindings = []
    }

    let private ssmFields : Ssm.Field list = [
        { Var = Ssm.Field ("f", Ssm.IntType); Init = [Ssm.IntVal 1; Ssm.IntVal 17; Ssm.IntVal -1] }
        { Var = Ssm.Field ("b", Ssm.BoolType); Init = [Ssm.BoolVal false; Ssm.BoolVal true] }
    ]

    let private scmFields : Scm.FieldDecl list = [
        { Field = Scm.Field "f"; Type = Scm.IntType; Init = [Scm.IntVal 1; Scm.IntVal 17; Scm.IntVal -1] }
        { Field = Scm.Field "b"; Type = Scm.BoolType; Init = [Scm.BoolVal false; Scm.BoolVal true] }
    ]

    let private ssmReqPort : Ssm.Method = {
        Name = "R"
        Params = [{ Var = Ssm.Arg ("a", Ssm.IntType); Direction = Ssm.InOut}; { Var = Ssm.Arg ("b", Ssm.BoolType); Direction = Ssm.In}]
        Body = Ssm.NopStm
        Return = Ssm.VoidType
        Locals = []
        Kind = Ssm.ReqPort
    }

    let private scmReqPort : Scm.ReqPortDecl = {
        ReqPort = Scm.ReqPort "R"
        Params = 
            [
                { Var = { Var = Scm.Var "a"; Type = Scm.IntType }; Dir = Scm.InOut }
                { Var = { Var = Scm.Var "b"; Type = Scm.BoolType }; Dir = Scm.In }
            ]
    }

    let private ssmProvPort : Ssm.Method = {
        Name = "M"
        Params = [{ Var = Ssm.Arg ("a", Ssm.IntType); Direction = Ssm.InOut}; { Var = Ssm.Arg ("b", Ssm.BoolType); Direction = Ssm.In}]
        Body = 
            Ssm.SeqStm [
                Ssm.IfStm (
                    Ssm.VarExpr (Ssm.Arg ("b", Ssm.BoolType)),
                    Ssm.AsgnStm (Ssm.Local ("x", Ssm.IntType), Ssm.IntExpr 1),
                    Ssm.SeqStm [
                        Ssm.ExprStm (Ssm.CallExpr ("R", [Ssm.IntType; Ssm.BoolType], [Ssm.InOut; Ssm.In], Ssm.VoidType, [Ssm.VarRefExpr (ssmFields.[0].Var); Ssm.BoolExpr false]))
                        Ssm.AsgnStm (Ssm.Local ("x", Ssm.IntType), Ssm.IntExpr -1)
                        Ssm.AsgnStm (Ssm.Field ("f", Ssm.BoolType), Ssm.BoolExpr false)
                    ]
                )
                Ssm.AsgnStm (Ssm.Arg ("a", Ssm.IntType), Ssm.VarExpr (Ssm.Local ("x", Ssm.IntType)))
            ]
        Return = Ssm.VoidType
        Locals = [Ssm.Local ("x", Ssm.IntType)]
        Kind = Ssm.ProvPort
    }

    let private scmProvPort : Scm.ProvPortDecl = {
        FaultExpr = None
        ProvPort = Scm.ProvPort "M"
        Params = 
            [
                { Var = { Var = Scm.Var "a"; Type = Scm.IntType }; Dir = Scm.InOut }
                { Var = { Var = Scm.Var "b"; Type = Scm.BoolType }; Dir = Scm.In }
            ]
        Behavior = 
        {
            Locals = [{ Var = Scm.Var "x"; Type = Scm.IntType }]
            Body = Scm.Block 
                [
                    Scm.Choice [
                        (Scm.ReadVar (Scm.Var "b"), Scm.AssignVar (Scm.Var "x", Scm.Literal (Scm.IntVal 1)))
                        (Scm.UExpr (Scm.ReadVar (Scm.Var "b"), Scm.Not), 
                            Scm.Block 
                                [
                                    Scm.CallPort (Scm.ReqPort "R", [Scm.InOutFieldParam scmFields.[0].Field; Scm.ExprParam (Scm.Literal (Scm.BoolVal false))])
                                    Scm.AssignVar (Scm.Var "x", Scm.Literal (Scm.IntVal -1))
                                    Scm.AssignField (Scm.Field "f", Scm.Literal (Scm.BoolVal false))
                                ])
                    ]
                    Scm.AssignVar (Scm.Var "a", Scm.ReadVar (Scm.Var "x"))
                ]
        }
    }

    let private ssmBindings : Ssm.Binding list = 
        [
            {
                SourceComp = "Root0.x.y"
                SourcePort = "A"
                TargetComp = "Root1.z.w"
                TargetPort = "B"
                Kind = BindingKind.Instantaneous
            }
            {
                SourceComp = "Root0.x.y"
                SourcePort = "A"
                TargetComp = "Root1.z.w"
                TargetPort = "B"
                Kind = BindingKind.Delayed
            }
        ]

    let private scmBindings : Scm.BndDecl list = 
        [
            {
                Source = { Comp = Scm.Comp "y" |> Some; ProvPort = Scm.ProvPort "A" }
                Target = { Comp = Scm.Comp "w" |> Some; ReqPort = Scm.ReqPort "B" }
                Kind = Scm.Instantaneous
            }
            {
                Source = { Comp = Scm.Comp "y" |> Some; ProvPort = Scm.ProvPort "A" }
                Target = { Comp = Scm.Comp "w" |> Some; ReqPort = Scm.ReqPort "B" }
                Kind = Scm.Delayed
            }
        ]

    let private ssmStep : Ssm.Method = {
        Name = "Update"
        Params = []
        Body = Ssm.AsgnStm (Ssm.Local ("x", Ssm.IntType), Ssm.IntExpr -1)
        Return = Ssm.VoidType
        Locals = [Ssm.Local ("x", Ssm.IntType)]
        Kind = Ssm.Step
    }

    let private scmStep : Scm.StepDecl = {
        FaultExpr = None
        Behavior = 
        {
            Locals = [{ Var = Scm.Var "x"; Type = Scm.IntType }]
            Body = Scm.AssignVar (Scm.Var "x", Scm.Literal (Scm.IntVal -1))
        }
    }

    let private transform = SsmToScm.transform

    [<Test>]
    let ``field transformation`` () =
        transform { ssmComp with Fields = ssmFields } =? { scmComp with Fields = scmFields }

    [<Test>]
    let ``required port transformation`` () =
        transform { ssmComp with Methods = [ssmReqPort] } =? { scmComp with ReqPorts = [scmReqPort] }

    [<Test>]
    let ``provided port transformation`` () =
        transform { ssmComp with Methods = [ssmProvPort] } =? { scmComp with ProvPorts = [scmProvPort] }

    [<Test>]
    let ``binding transformation`` () =
        transform { ssmComp with Bindings = ssmBindings } =? { scmComp with Bindings = scmBindings }

    [<Test>]
    let ``step method transformation`` () =
        transform { ssmComp with Methods = [ssmStep] } =? { scmComp with Steps = [scmStep] }

    [<Test>]
    let ``nested components`` () =
        let ssm = {
            ssmComp with
             Fields = ssmFields
             Methods = [ssmProvPort; ssmReqPort; ssmStep]
             Bindings = ssmBindings
        }
        let sub = { ssm with Subs = [ssm; ssm] }
        let ssm = { ssm with Subs = [sub; { ssm with Bindings = ssmBindings; Methods = [ssmStep; ssmProvPort] }] }

        let scm = {
            scmComp with
             Fields = scmFields
             ReqPorts = [scmReqPort]
             ProvPorts = [scmProvPort]
             Steps = [scmStep]
             Bindings = scmBindings
        }
        let sub = { scm with Subs = [scm; scm] }
        let scm = { scm with Subs = [sub; { scm with Bindings = scmBindings; Steps = [scmStep]; ProvPorts = [scmProvPort]; ReqPorts = [] }] }

        transform ssm =? scm