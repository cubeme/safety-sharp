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

        
    [<RequireQualifiedAccessAttribute>]
    type internal LocExpr = // expression with location //TODO: Maybe split into LocAtom and LocExpr. Makes LTL and CTL easier
        | Literal of Val
        | ReadField of CompPath * Field
        | ReadFault of CompPath * Fault
        | ReadOldField of CompPath * Field
        | ReadOldFault of CompPath * Fault
        | ReadVar of Var // no path here, because only local! Also we do not assume a previous valuation!
        | UExpr of LocExpr * UOp
        | BExpr of LocExpr * BOp * LocExpr

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
        
    [<RequireQualifiedAccessAttribute>]
    type internal Contract = 
        | None
        | AutoDeriveChanges of Requires : (LocExpr option) * Ensures : (LocExpr option) // if not declared explicitly, derive it implicitly. All variables written to by port and called ports. Writing it explicitly ensures, that ports being called, which are in _this_ component, make nothing wrong in this component. They may do everything when they live in their own component. Some kind of "Set.union port1.Changed port2.Changed "TODO: exact semantics. InferFrameAssumption
        | Full              of Requires : (LocExpr option) * Ensures : (LocExpr option) * ChangedFields : (Field list) * ChangedFaults : (Fault list) //with frame assumption. ExplicitFrameAssumption
        // | FullResilientTo of Requires : (LocExpr option) * Ensures : (LocExpr option) * ChangedFields : (Field list) * ChangedFaults : (Fault list) * ResilientToFaults : (Fault list)
        // | FullVulnerableTo of Requires : (LocExpr option) * Ensures : (LocExpr option) * ChangedFields : (Field list) * ChangedFaults : (Fault list) * VulnerableToFaults : (Fault list)

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
        //Contract : Contract
    }

    type internal ProvPortDecl = {
        FaultExpr : FaultExpr option
        ProvPort : ProvPort
        Params : ParamDecl list
        Behavior : BehaviorDecl
        Contract : Contract
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
        //Contract : Contract
    }

    type internal StepDecl = {
        FaultExpr : FaultExpr option
        Behavior : BehaviorDecl
        Contract : Contract
    }        

    type internal CompDecl = {
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
            with
                override traceable.ToString() =
                    let compPathStr (compPath:CompPath) =
                        compPath |> List.rev |> List.map (fun (Comp(comp)) -> comp+".") |> String.concat ""
                    match traceable with
                        | TraceableField(compPath,Field.Field(field)) -> sprintf "field '%s%s'" (compPathStr compPath) (field)
                        | TraceableFault(compPath,Fault.Fault(fault)) -> sprintf "fault '%s%s'" (compPathStr compPath) (fault)

    type internal ScmModel =
        ScmModel of CompDecl
            with
                interface IModel<Traceable> with
                    member this.getTraceables : Traceable list =
                        let rec collectGlobalVariables (parentPath:CompPath) (currentCompDecl:CompDecl) : Traceable list =
                            let currentPath = (currentCompDecl.Comp)::parentPath
                            let varsFromSubs = currentCompDecl.Subs |> List.collect (collectGlobalVariables currentPath)
                            let varsFromHere =
                                let varsFromFields = currentCompDecl.Fields |> List.map (fun field -> Traceable.TraceableField(currentPath,field.Field) )
                                let varsFromFaults = currentCompDecl.Faults |> List.map (fun fault -> Traceable.TraceableFault(currentPath,fault.Fault) )
                                (varsFromFields@varsFromFaults)
                            (varsFromHere@varsFromSubs)
                        let rootComponent = this.getRootComp
                        collectGlobalVariables []  (rootComponent)
                member this.getTraceables : Traceable list  =
                    let imodel = this :> IModel<Traceable>
                    imodel.getTraceables
                member model.getRootComp = match model with | ScmModel(rootComp) -> rootComp
