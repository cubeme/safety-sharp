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

namespace SafetySharp.Models

module internal Scm =

    type internal Var = Var of string
    type internal Field = Field of string
    type internal ReqPort = ReqPort of string
    type internal ProvPort = ProvPort of string
    type internal Fault = Fault of string
    type internal Comp = Comp of string

    type CompPath = Comp list // index1::index2::root::[]

    type internal UOp =
        | Minus
        | Not

    type internal BOp =
        | Add
        | Subtract
        | Multiply
        | Divide
        | Modulo
        | And
        | Or
        | Equals
        | NotEquals
        | Less
        | LessEqual
        | Greater
        | GreaterEqual

    type internal Val = 
        | BoolVal of bool
        | IntVal of int

    type internal Expr =
        | Literal of Val
        | ReadVar of Var
        | ReadField of Field
        | UExpr of Expr * UOp
        | BExpr of Expr * BOp * Expr

    type internal FaultExpr =
        | Fault of Fault
        | NotFault of FaultExpr
        | AndFault of FaultExpr * FaultExpr
        | OrFault of FaultExpr * FaultExpr
        
    type internal Param =
        | ExprParam of Expr
        | InOutVarParam of Var
        | InOutFieldParam of Field

    type internal Stm =
        | AssignVar of Var * Expr
        | AssignField of Field * Expr
        | AssignFault of Fault * Expr
        | Block of Stm list
        | Choice of (Expr * Stm) list
        | CallPort of ReqPort * Param list
        | StepComp of Comp
        | StepFault of Fault

    type internal Type =
        | BoolType
        | IntType

    type internal VarDecl = {
        Var : Var
        Type : Type
    }

    type internal FieldDecl = {
        Field : Field
        Type : Type
        Init : Val list 
    }

    type internal BehaviorDecl = {
        Locals : VarDecl list
        Body : Stm
    }

    type internal ParamDir = 
        | In
        | InOut

    type internal ParamDecl = {
        Var : VarDecl
        Dir : ParamDir
    }

    type internal ReqPortDecl = {
        ReqPort : ReqPort
        Params : ParamDecl list
    }

    type internal ProvPortDecl = {
        FaultExpr : FaultExpr option
        ProvPort : ProvPort
        Params : ParamDecl list
        Behavior : BehaviorDecl
    }

    type internal BndSrc = {
        ProvPort : ProvPort
        Comp : CompPath
    }

    type internal BndTarget = {
        ReqPort : ReqPort
        Comp : CompPath
    }

    type internal BndKind = 
        | Instantaneous
        | Delayed

    type internal BndDecl = {
        Target : BndTarget
        Source : BndSrc
        Kind : BndKind
    }

    type internal FaultDecl = {
        Fault : Fault
        Step : BehaviorDecl //TODO: maybe rename to Behavior to be consistent
    }

    type internal StepDecl = {
        FaultExpr : FaultExpr option
        Behavior : BehaviorDecl
    }
    
    [<RequireQualifiedAccessAttribute>]
    type internal LocExpr = // expression with location
        | Literal of Val
        | ReadField of CompPath * Field
        | ReadFault of CompPath * Fault
        | UExpr of LocExpr * UOp
        | BExpr of LocExpr * BOp * LocExpr
    
    type internal Formula =
        | Invariant of Invariant:LocExpr
        | RG of Rely:LocExpr * Guarantee:LocExpr
        | DCCA of FaultsToConsider:(CompPath*Fault) list
        //| LTL of LtlExpression
        // | CTL of CtlExpression
        // | PCtl of PCtlExpression

    type internal CompDecl = {
        Comp : Comp
        Subs : CompDecl list
        Fields : FieldDecl list
        Faults : FaultDecl list
        ReqPorts : ReqPortDecl list
        ProvPorts : ProvPortDecl list
        Bindings : BndDecl list
        Steps : StepDecl list
        Formulas : Formula list
    }