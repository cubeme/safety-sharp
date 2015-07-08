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

module Scm =

    type Var = Var of string
    type Field = Field of string
    type ReqPort = ReqPort of string
    type ProvPort = ProvPort of string
    type Fault = Fault of string
    type Comp = Comp of string
    
    type CompPath = Comp list // index1::index2::root::[]

    type UOp =
        | Minus
        | Not

    type BOp =
        | Add
        | Subtract
        | Multiply
        | Divide
        | Modulo
        | And
        | Or
        | Equal
        | NotEqual
        | Less
        | LessEqual
        | Greater
        | GreaterEqual

    type Val = 
        | BoolVal of bool
        | IntVal of int
        | RealVal of double
        | ProbVal of double

        
    [<RequireQualifiedAccessAttribute>]
    type Element =
        | Field of Field
        | Var of Var
        //| Indexed of Container:Element * Index:Expr
        // Example 1: "fieldArray : Array<2,bool>". Access "fieldArray[1]"
        //            let field = Field.Field("fieldArray")
        //            let expr1 = Expr.Literal(Val.IntVal(1))
        //            ComplexElementAccess.SubContainer( ComplexElementAccess.Field(field),expr1)
        // Example 2: "fieldArray : Array<2,bool>". Access "fieldArray[expr]". "expr" may be the current value of a field.
        //            let field = Field.Field("fieldArray")
        //            ComplexElementAccess.SubContainer( ComplexElementAccess.Field(field),expr))
        // Example 3: "fieldArray : Array<1,Array<2,bool>>". Access "fieldArray[0][1]".
        //            let field = Field.Field("fieldArray")
        //            let expr0 = Expr.Literal(Val.IntVal(0))
        //            let expr1 = Expr.Literal(Val.IntVal(1))
        //            ComplexElementAccess.SubContainer(ComplexElementAccess.SubContainer( ComplexElementAccess.Field(field),expr0),expr1)
        
    and Expr =
        | Literal of Val
        | Read of Element //Arrays of Fields, Arrays of Arrays of Vars...
        | UExpr of Expr * UOp
        | BExpr of Expr * BOp * Expr
        //| Forall of Elements:(Element list) * NewVarsInSubExpr:(Var list) * SubExpr:Expr
        //| Exists of Elements:(Element list) * NewVarsInSubExpr:(Var list) * SubExpr:Expr
        
    type FaultExpr =
        | Fault of Fault
        | NotFault of FaultExpr
        | AndFault of FaultExpr * FaultExpr
        | OrFault of FaultExpr * FaultExpr
        
    type Param =
        | ExprParam of Expr
        | InOutElementParam of Element
        
    type Stm =
        | AssignElement of Element * Expr
        | AssignFault of Fault * Expr
        | Block of Stm list
        | Choice of (Expr * Stm) list
        | Stochastic of (Expr * Stm) list //Expr must be of type ProbVal
        | CallPort of ReqPort * Param list
        | StepComp of Comp
        | StepFault of Fault
        //| Foreach of Elements:(Element list) * NewVarsInSubExpr:(Var list) * SubStm:Stm
        
    type OverflowBehavior =
        | Clamp = 0
        | WrapAround = 1
        | Error = 2

    type Type =
        | BoolType
        | IntType // When used as type of a field it shows that the value is unrestricted. Model checker must support this. But may also be used in local variables/parameters, which get inlined, and thus may also be replaced by a RangedIntType during the inlining.
        | RealType // Same restrictions as for IntType
        | RangedIntType of From:int * To:int * Overflow:OverflowBehavior // "intValue1: int<0..100>; intValue2: int<0..100,clamp on overrun>; intValue3: int<0..100,wrap around on overrun>; intValue4: int<0..100,error on overrun>"
        | RangedRealType of From:double  * To:double * Overflow:OverflowBehavior
        // | RangedMeasure of Unit:DerivedSiType * From:double * To:double "length1: measure<m><0..100>; speed1: measure<m/s><0..4>; acc1:measure<m/s²>"
        // | DerivedMeasures (may be given an initial value. assignments may only be reseted) "time1: measure<s,auto tick>; speed2: measure<m/s,based on acc1>; position1: measure<m,based on speed 2>"
        // | ArrayType of Size:int * ElementType:Type // May be used for field, local vars and parameters. 0-based.
        // | ArrayOfUnspecifiedSizeType of ElementType:Type // May be used in parameters only.  Are replaced by a ArrayType with a defined size during the inlining. Thus they are not usable for field or local vars.
        
    [<RequireQualifiedAccessAttribute>]
    type LocElement = // Extension of Element with Location. For detailed examples of the idea see description of ComplexElementAccess
        | Field of CompPath * Field
        | LocalVar of Var // no path here, because only local! Also we do not assume a previous valuation!
        //| Indexed of Container:(CompPath*LocElement) * Index:LocExpr

    and [<RequireQualifiedAccessAttribute>] LocExpr = // expression with location
        | Literal of Val
        | Read of LocElement //Arrays of Fields, Arrays of Arrays of Vars...
        | ReadFault of CompPath * Fault
        | ReadOld of LocElement //Arrays of Fields, Arrays of Arrays of Vars...
        | ReadOldFault of CompPath * Fault
        | UExpr of LocExpr * UOp
        | BExpr of LocExpr * BOp * LocExpr
    
    [<RequireQualifiedAccessAttribute>]
    type Contract = 
        | None
        | AutoDeriveChanges of Requires : (LocExpr option) * Ensures : (LocExpr option) // if not declared explicitly, derive it implicitly. All variables written to by port and called ports. Writing it explicitly ensures, that ports being called, which are in _this_ component, make nothing wrong in this component. They may do everything when they live in their own component. Some kind of "Set.union port1.Changed port2.Changed "TODO: exact semantics. InferFrameAssumption
        | Full              of Requires : (LocExpr option) * Ensures : (LocExpr option) * ChangedFields : (Field list) * ChangedFaults : (Fault list) //with frame assumption. ExplicitFrameAssumption
        // | FullResilientTo of Requires : (LocExpr option) * Ensures : (LocExpr option) * ChangedFields : (Field list) * ChangedFaults : (Fault list) * ResilientToFaults : (Fault list)
        // | FullVulnerableTo of Requires : (LocExpr option) * Ensures : (LocExpr option) * ChangedFields : (Field list) * ChangedFaults : (Fault list) * VulnerableToFaults : (Fault list)

    type VarDecl = {
        Var : Var
        Type : Type
    }

    type FieldDecl = {
        Field : Field
        Type : Type
        Init : Val list 
    }

    type BehaviorDecl = {
        Locals : VarDecl list
        Body : Stm
    }

    type ParamDir = 
        | In
        | InOut

    type ParamDecl = {
        Var : VarDecl
        Dir : ParamDir
    }

    type ReqPortDecl = {
        ReqPort : ReqPort
        Params : ParamDecl list
        //Contract : Contract
    }

    type ProvPortDecl = {
        FaultExpr : FaultExpr option
        ProvPort : ProvPort
        Params : ParamDecl list
        Behavior : BehaviorDecl
        Contract : Contract
    }

    type BndSrc = {
        ProvPort : ProvPort
        Comp : CompPath
    }

    type BndTarget = {
        ReqPort : ReqPort
        Comp : CompPath
    }

    type BndKind = 
        | Instantaneous
        | Delayed

    type BndDecl = {
        Target : BndTarget
        Source : BndSrc
        Kind : BndKind
    }

    type FaultDecl = {
        Fault : Fault
        Step : BehaviorDecl //TODO: maybe rename to Behavior to be consistent
        //Contract : Contract
    }

    type StepDecl = {
        FaultExpr : FaultExpr option
        Behavior : BehaviorDecl
        Contract : Contract
    }        

    type CompDecl = {
        Comp : Comp
        Subs : CompDecl list
        Fields : FieldDecl list
        Faults : FaultDecl list
        ReqPorts : ReqPortDecl list
        ProvPorts : ProvPortDecl list
        Bindings : BndDecl list
        Steps : StepDecl list
    }

    type Traceable = // this is necessary for tracing of changes
        | TraceableField of CompPath * Field
        | TraceableFault of CompPath * Fault
        | TraceableRemoved of Reason:string
            with
                override traceable.ToString() =
                    let compPathStr (compPath:CompPath) =
                        compPath |> List.rev |> List.map (fun (Comp(comp)) -> comp+".") |> String.concat ""
                    match traceable with
                        | TraceableField(compPath,Field.Field(field)) -> sprintf "field '%s%s'" (compPathStr compPath) (field)
                        | TraceableFault(compPath,Fault.Fault(fault)) -> sprintf "fault '%s%s'" (compPathStr compPath) (fault)
                        | TraceableRemoved(reason) -> sprintf "removed (reason:%s)" (reason)

    type ScmModel =
        ScmModel of CompDecl
