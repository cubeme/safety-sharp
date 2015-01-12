// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

namespace SafetySharp.Models.Scm

// TODO: syntax must be adapted and indention should be added (make it readable)
// TODO: write tests


module internal ScmAstToString =
    
    let exportVar (var:Var) : string =
        match var with
            | Var(str) -> str

    let exportField (field:Field) =
        match field with
            | Field (str) -> str
            
    let exportReqPort (reqPort:ReqPort) : string =
        match reqPort with
            | ReqPort (str) -> str

    let exportProvPort (provPort:ProvPort) : string =
        match provPort with
            | ProvPort (str) -> str

    let exportFault (fault:Fault) : string =
        match fault with
            | Fault.Fault (str) -> str

    let exportComp (comp:Comp) : string =
        match comp with 
            | Comp (str) -> str

    let exportUOp (uop:UOp) : string =
        match uop with
            | UOp.Minus -> "-"
            | UOp.Not -> "!"

    let exportBOp (bop:BOp) : string =
        match bop with
            | BOp.Add -> "+"
            | BOp.Subtract -> "-"
            | BOp.Multiply -> "*"
            | BOp.Divide -> "/"
            | BOp.Modulo -> "%"
            | BOp.And -> "&&"
            | BOp.Or -> "||"
            | BOp.Equals -> "=="
            | BOp.NotEquals -> "!="
            | BOp.Less -> "<"
            | BOp.LessEqual -> "<="
            | BOp.Greater -> ">"
            | BOp.GreaterEqual -> ">="

    let exportVal (_val:Val) : string =
        match _val with
            | Val.BoolVal (_val) -> _val.ToString()
            | Val.IntVal (_val) -> _val.ToString()

    let rec exportExpr (expr:Expr) : string =
        match expr with
            | Expr.Literal (_val) -> exportVal _val
            | Expr.ReadVar (_var) -> exportVar _var
            | Expr.ReadField (field) -> exportField field
            | Expr.UExpr (expr,uop) -> sprintf "%s(%s)" (exportUOp uop) (exportExpr expr)
            | Expr.BExpr (exprLeft, bop, exprRight) -> sprintf "(%s) %s (%s)" (exportExpr exprLeft) (exportBOp bop) (exportExpr exprRight)

    let rec exportFaultExpr (faultExpr:FaultExpr) : string =
        match faultExpr with
            | FaultExpr.Fault (fault) -> exportFault fault
            | FaultExpr.NotFault (faultExpr) -> sprintf "!(%s)" (exportFaultExpr faultExpr)
            | FaultExpr.AndFault (faultExprLeft,faultExprRight) -> sprintf "(%s) || (%s)" (exportFaultExpr faultExprLeft) (exportFaultExpr faultExprRight)
            | FaultExpr.OrFault (faultExprLeft,faultExprRight) -> sprintf "(%s) || (%s)" (exportFaultExpr faultExprLeft) (exportFaultExpr faultExprRight)

    let exportParam (_param:Param) : string =
        match _param with
            | Param.ExprParam (expr) -> sprintf "in %s" (exportExpr expr)
            | Param.InOutVarParam (_var) -> sprintf "inout %s" (exportVar _var)
            | Param.InOutFieldParam (field) -> sprintf "inout %s" (exportField field)

    let rec exportStm (stm:Stm) : string =
        match stm with
            | Stm.AssignVar (var,expr) ->
                sprintf "%s := %s;" (exportVar var) (exportExpr expr)
            | Stm.AssignField (field,expr) ->
                sprintf "%s := %s;" (exportField field) (exportExpr expr)
            | Stm.AssignFault (fault,expr) ->
                sprintf "%s := %s;" (exportFault fault) (exportExpr expr)
            | Stm.Block (stmts) ->
                let stmts = stmts |> List.map exportStm |> String.concat ";"
                sprintf "{%s}" stmts
            | Stm.Choice (choices:(Expr * Stm) list) ->
                let choices = choices |> List.map (fun (guard,stm) -> sprintf "(%s) -> {%s}" (exportExpr guard) (exportStm stm))
                                      |> String.concat ""
                sprintf "choice { %s }" choices
            | Stm.CallPort (reqPort, _params) ->
                let _params = _params |> List.map exportParam
                                      |> String.concat ","
                sprintf "%s (%s);" (exportReqPort reqPort) (_params)
            | Stm.StepComp (comp) ->
                sprintf "step %s;" (exportComp comp)
            | Stm.StepFault (fault) ->
                sprintf "step %s;" (exportFault fault)
      
    let exportType (_type:Type) : string =
        match _type with
            | BoolType -> "bool"
            | IntType -> "int"

    let exportVarDecl (varDecl:VarDecl) : string =
        sprintf "%s %s" (exportType varDecl.Type) (exportVar varDecl.Var)

    let exportFieldDecl (fieldDecl:FieldDecl): string =
        let initVars = fieldDecl.Init |> List.map exportVal |> String.concat ","
        sprintf "%s %s = %s;" (exportType fieldDecl.Type) (exportField fieldDecl.Field) (initVars)


    
    let exportBehaviorDecl (behaviorDecl:BehaviorDecl) : string =
        let locals = behaviorDecl.Locals |> List.map exportVarDecl |> String.concat ";"        
        sprintf "%s %s" (locals) (exportStm behaviorDecl.Body)

    let exportParamDir (paramDir:ParamDir) : string = 
        match paramDir with
            | In -> "in"
            | InOut -> "inout"

    let exportParamDecl (paramDecl:ParamDecl) : string = 
        sprintf "%s %s" (exportParamDir paramDecl.Dir) (exportVarDecl paramDecl.Var)

    let exportReqPortDecl (reqPortDecl:ReqPortDecl) : string =
        let _params = reqPortDecl.Params |> List.map exportParamDecl
                                         |> String.concat ","
        sprintf "%s(%s);" (exportReqPort reqPortDecl.ReqPort) (_params)


    let exportProvPortDecl (provPortDecl:ProvPortDecl) : string =
        let faultExpr =
            match provPortDecl.FaultExpr with
                | None -> ""
                | Some (faultExpr) -> exportFaultExpr faultExpr
        let _params = provPortDecl.Params |> List.map exportParamDecl
                                          |> String.concat ","
        sprintf "[%s]%s(%s) {%s}" faultExpr (exportProvPort provPortDecl.ProvPort) (_params) (exportBehaviorDecl provPortDecl.Behavior)


    let exportBndSrc (bndSrc:BndSrc) : string =
        match bndSrc.Comp with
            | None -> exportProvPort bndSrc.ProvPort
            | Some (comp) -> sprintf "%s.%s" (exportComp comp) (exportProvPort bndSrc.ProvPort)

    let exportBndTarget (bndTarget:BndTarget) : string =
        match bndTarget.Comp with
            | None -> exportReqPort bndTarget.ReqPort
            | Some (comp) -> sprintf "%s.%s" (exportComp comp) (exportReqPort bndTarget.ReqPort)

    let exportBndKind (bndKind:BndKind) : string =
        match bndKind with
            | BndKind.Instantaneous -> "instantly"
            | BndKind.Delayed -> "delayed"

    let exportBndDecl (bndDecl:BndDecl) : string =
        sprintf "%s = %s %s;" (exportBndTarget bndDecl.Target) (exportBndKind bndDecl.Kind) (exportBndSrc bndDecl.Source)

    let exportFaultDecl (faultDecl:FaultDecl) : string =
        sprintf "fault %s { %s }" (exportFault faultDecl.Fault) (exportBehaviorDecl faultDecl.Step)

    let exportStepDecl (stepDecl:StepDecl) : string =
        let faultExpr =
            match stepDecl.FaultExpr with
                | None -> ""
                | Some (faultExpr) -> exportFaultExpr faultExpr
        sprintf "step %s { %s }" (faultExpr) (exportBehaviorDecl stepDecl.Behavior)


    let rec exportCompDecl (compDecl:CompDecl) : string =
        sprintf "%s %s %s %s %s %s %s %s"
                (exportComp compDecl.Comp)
                (compDecl.Subs |> List.map exportCompDecl |> String.concat "")
                (compDecl.Fields |> List.map exportFieldDecl |> String.concat "")
                (compDecl.Faults |> List.map exportFaultDecl |> String.concat "")
                (compDecl.ReqPorts |> List.map exportReqPortDecl |> String.concat "")
                (compDecl.ProvPorts |> List.map exportProvPortDecl |> String.concat "")
                (compDecl.Bindings |> List.map exportBndDecl |> String.concat "")
                (compDecl.Steps |> List.map exportStepDecl |> String.concat "")
     
     
