﻿// The MIT License (MIT)
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
    
    type NewLineStyle =
        | NoNewLine
        | NewLine
        | NewParagraph

    type AstToStringState = {
        Indent : int;
        NewLines : int;
        CurrentLine : string;
        TextBuffer : string list;
    }
        with
            static member initial =
                {
                    AstToStringState.Indent = 0;
                    AstToStringState.NewLines = 0;
                    AstToStringState.CurrentLine = "";
                    AstToStringState.TextBuffer = [];
                }                
            override state.ToString() : string =
                (state.CurrentLine :: state.TextBuffer)
                    |> List.rev
                    |> String.concat System.Environment.NewLine

    type AstToStringStateFunction = AstToStringState -> AstToStringState
    
    

    //////////////////////////////////////////////////////////////////////////////
    // helpers
    //////////////////////////////////////////////////////////////////////////////

    //elementary

    let increaseIndent (state:AstToStringState) : AstToStringState =
        { state with
            AstToStringState.Indent = state.Indent + 1;
        }
    let decreaseIndent (state:AstToStringState) : AstToStringState =
        { state with
            AstToStringState.Indent = state.Indent - 1;
        }
    let newLine (state:AstToStringState) : AstToStringState =
        { state with
            AstToStringState.Indent = state.Indent + 1;
        }
    let newLineAndIncreaseIndent (state:AstToStringState) : AstToStringState =
        { state with
            AstToStringState.Indent = state.Indent + 1;
        }
    let newLineAndDecreaseIndent (state:AstToStringState) : AstToStringState =
        { state with
            AstToStringState.Indent = state.Indent + 1;
        }
    let newParagraph (state:AstToStringState) : AstToStringState =
        { state with
            AstToStringState.Indent = state.Indent + 1;
        }
    let append (str:string) (state:AstToStringState) : AstToStringState =
        { state with
            AstToStringState.CurrentLine = state.CurrentLine + str;
        }

    let rec foreach (elements:'a list) (writer: 'a -> AstToStringState -> AstToStringState) (state:AstToStringState): AstToStringState =
        if elements.IsEmpty then
            state
        else
            let newState = writer elements.Head state
            foreach elements.Tail writer newState

    let rec foreachWithSep  (elements:'a list) (writer: 'a -> AstToStringState -> AstToStringState) (sep:AstToStringState -> AstToStringState) (state:AstToStringState): AstToStringState =
        if elements.IsEmpty then
            state
        else if elements.Tail.IsEmpty then
            writer elements.Head state
        else
            let newState1 = writer elements.Head state
            let newState2 = sep newState1
            foreach elements.Tail writer newState2

    
    // Inspired by FParsec's createParserForwardedToRef (defined in FParsec/Primitives.fs)
    let createWriterForwardedToRef() =
        let dummyWriter = fun (state:AstToStringState) ->
            failwith "the writerRef needs to be replaced by a real implementation"
        let w = ref dummyWriter
        ((fun state -> !w state), w) : AstToStringStateFunction * AstToStringStateFunction ref

    // this one gets executed automatically (see definition of (>>=) )
    let appendTrail (state:AstToStringState) : AstToStringState =
        { state with
            AstToStringState.Indent = state.Indent + 1;
        }
    

    // Inspired by http://fsharpforfunandprofit.com/posts/computation-expressions-bind/
    let (>>=) (m:AstToStringStateFunction)
              (f:AstToStringStateFunction)
              (state:AstToStringState) : AstToStringState =
        let newState = m state
        let newStateWithTrail = appendTrail newState
        f newStateWithTrail
    
    //////////////////////////////////////////////////////////////////////////////
    // actual export
    //////////////////////////////////////////////////////////////////////////////
     


    let exportVar (var:Var) : AstToStringStateFunction =
        let toAppend =
            match var with
                | Var(str) -> str
        append toAppend

    let exportField (field:Field) : AstToStringStateFunction =
        let toAppend =
            match field with
                | Field (str) -> str
        append toAppend
            
    let exportReqPort (reqPort:ReqPort) : AstToStringStateFunction =
        let toAppend =
            match reqPort with
                | ReqPort (str) -> str
        append toAppend

    let exportProvPort (provPort:ProvPort) : AstToStringStateFunction =
        let toAppend =
            match provPort with
                | ProvPort (str) -> str
        append toAppend

    let exportFault (fault:Fault) : AstToStringStateFunction =
        let toAppend =
            match fault with
                | Fault.Fault (str) -> str
        append toAppend

    let exportComp (comp:Comp) : AstToStringStateFunction =
        let toAppend =
            match comp with 
                | Comp (str) -> str
        append toAppend

    let exportUOp (uop:UOp) : AstToStringStateFunction =
        let toAppend =
            match uop with
                | UOp.Minus -> "-"
                | UOp.Not -> "!"
        append toAppend

    let exportBOp (bop:BOp) : AstToStringStateFunction =
        let toAppend =
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
        append toAppend

    let exportVal (_val:Val) : AstToStringStateFunction =
        let toAppend =
            match _val with
                | Val.BoolVal (_val) -> _val.ToString()
                | Val.IntVal (_val) -> _val.ToString()
        append toAppend

    let rec exportExpr (expr:Expr) : AstToStringStateFunction =
        match expr with
            | Expr.Literal (_val) -> exportVal  _val
            | Expr.ReadVar (_var) -> exportVar  _var
            | Expr.ReadField (field) -> exportField  field
            | Expr.UExpr (expr,uop) ->                
                //sprintf "%s(%s)" (exportUOp state uop)  (exportExpr state expr)
                (exportUOp uop) >>= (append "(") >>= (exportExpr expr) >>= (append ")")
            | Expr.BExpr (exprLeft, bop, exprRight) ->
                (append "(") >>= (exportExpr exprLeft) >>= (append ")")  >>=
                (exportBOp bop) >>=
                (append "(") >>= (exportExpr exprRight) >>= (append ")") 

                
    let rec exportFaultExpr (faultExpr:FaultExpr) : AstToStringStateFunction =
        match faultExpr with
            | FaultExpr.Fault (fault) -> exportFault fault
            | FaultExpr.NotFault (faultExpr) ->
                (append "!(") >>= (exportFaultExpr faultExpr) >>= (append ")")
            | FaultExpr.AndFault (faultExprLeft,faultExprRight) ->
                (append "(") >>= (exportFaultExpr faultExprLeft) >>= (append ")")  >>=
                (append "&&") >>=
                (append "(") >>= (exportFaultExpr faultExprRight) >>= (append ")")
            | FaultExpr.OrFault (faultExprLeft,faultExprRight) ->
                (append "(") >>= (exportFaultExpr faultExprLeft) >>= (append ")")  >>=
                (append "||") >>=
                (append "(") >>= (exportFaultExpr faultExprRight) >>= (append ")")

    let exportParam (_param:Param) : AstToStringStateFunction =
        match _param with
            | Param.ExprParam (expr) ->
                (append "in ") >>=
                (exportExpr expr)
            | Param.InOutVarParam (_var) ->
                (append "inout ") >>=
                (exportVar _var)
            | Param.InOutFieldParam (field) ->
                (append "inout ") >>=
                (exportField field)
            
    let rec exportStm (stm:Stm) : AstToStringStateFunction =
        match stm with
            | Stm.AssignVar (var,expr) ->
                (exportVar var) >>=
                (append " := ") >>=
                (exportExpr expr) >>=
                (append "; ")
            | Stm.AssignField (field,expr) ->
                (exportField field) >>=
                (append " := ") >>=
                (exportExpr expr) >>=
                (append "; ")
            | Stm.AssignFault (fault,expr) ->
                (exportFault fault) >>=
                (append " := ") >>=
                (exportExpr expr) >>=
                (append "; ")
            | Stm.Block (stmts) ->
                (append " { ") >>= newLineAndIncreaseIndent >>=
                (foreach stmts (fun stm -> exportStm stm >>= newLine)) >>=
                (append " } ") >>= newLineAndDecreaseIndent
            | Stm.Choice (choices:(Expr * Stm) list) ->
                (append " choice {") >>= newLineAndIncreaseIndent >>=
                (foreach choices (fun (guard,stm) -> 
                                       exportExpr guard >>= append " => " >>= exportStm stm >>= newLine)
                                 ) >>=
                (append " choice }") >>= newLineAndDecreaseIndent
                
            | Stm.CallPort (reqPort, _params) ->
                (exportReqPort reqPort) >>=
                (append " ( ") >>=
                (foreachWithSep _params exportParam (append ",") ) >>=
                (append ");")
            | Stm.StepComp (comp) ->
                (append "step ") >>=
                (exportComp comp) >>=
                (append ";")
            | Stm.StepFault (fault) ->
                (append "step ") >>=
                (exportFault fault) >>=
                (append ";")
      
    let exportType (_type:Type) : AstToStringStateFunction =
        match _type with
            | BoolType -> append "bool"
            | IntType -> append "int"

    let exportVarDecl (varDecl:VarDecl) : AstToStringStateFunction =
        (exportType varDecl.Type) >>=
        (append " ") >>=
        (exportVar varDecl.Var)

    let exportFieldDecl (fieldDecl:FieldDecl): AstToStringStateFunction =
        (exportType fieldDecl.Type) >>=
        (append " ") >>=
        (exportField fieldDecl.Field) >>=
        (append " ") >>=
        (foreachWithSep fieldDecl.Init exportVal (append ",") )
    
    let exportBehaviorDecl (behaviorDecl:BehaviorDecl) : AstToStringStateFunction =
        (foreach behaviorDecl.Locals (fun var -> exportVarDecl var >>= (append ";")) ) >>=
        (append " ") >>=
        (exportStm behaviorDecl.Body)
        

    let exportParamDir (paramDir:ParamDir) : AstToStringStateFunction = 
        match paramDir with
            | In -> append "in"
            | InOut -> append "inout"
            
    let exportParamDecl (paramDecl:ParamDecl) : AstToStringStateFunction = 
        (exportParamDir paramDecl.Dir) >>=
        append " " >>=
        (exportVarDecl paramDecl.Var)

    let exportReqPortDecl (reqPortDecl:ReqPortDecl) : AstToStringStateFunction =
        (exportReqPort reqPortDecl.ReqPort) >>=
        (append "(") >>=
        (foreachWithSep reqPortDecl.Params exportParamDecl (append ",") ) >>=
        (append ");")

    let exportProvPortDecl (provPortDecl:ProvPortDecl) : AstToStringStateFunction =
        let faultExpr =
            match provPortDecl.FaultExpr with
                | None -> id
                | Some (faultExpr) -> (append "[") >>= (exportFaultExpr faultExpr) >>= (append "]")
        faultExpr >>=
        (exportProvPort provPortDecl.ProvPort) >>=
        (append "(") >>=
        (foreachWithSep provPortDecl.Params exportParamDecl (append ",") ) >>=
        (append ") {")>>=
        (exportBehaviorDecl provPortDecl.Behavior) >>=
        (append "}")

        
    let exportBndSrc (bndSrc:BndSrc) : AstToStringStateFunction =
        match bndSrc.Comp with
            | None ->
                exportProvPort bndSrc.ProvPort
            | Some (comp) ->
                (exportComp comp) >>=
                (append ".") >>=
                (exportProvPort bndSrc.ProvPort)

    let exportBndTarget (bndTarget:BndTarget) : AstToStringStateFunction =
        match bndTarget.Comp with
            | None ->
                exportReqPort bndTarget.ReqPort
            | Some (comp) ->
                (exportComp comp) >>=
                (append ".") >>=
                (exportReqPort bndTarget.ReqPort)

    let exportBndKind (bndKind:BndKind) : AstToStringStateFunction =
        match bndKind with
            | BndKind.Instantaneous -> append "instantly"
            | BndKind.Delayed -> append "delayed"
      
    let exportBndDecl (bndDecl:BndDecl) : AstToStringStateFunction =
        (exportBndTarget bndDecl.Target) >>=
        (append " = ") >>=
        (exportBndKind bndDecl.Kind) >>=
        (append " ")>>=
        (exportBndSrc bndDecl.Source) >>=
        (append ";")

    let exportFaultDecl (faultDecl:FaultDecl) : AstToStringStateFunction =
        (append "fault ") >>=
        (exportFault faultDecl.Fault) >>=
        (append " {")>>=
        (exportBehaviorDecl faultDecl.Step) >>=
        (append "}")
              
    let exportStepDecl (stepDecl:StepDecl) : AstToStringStateFunction =    
        let faultExpr =
            match stepDecl.FaultExpr with
                | None -> id
                | Some (faultExpr) -> (append "[") >>= (exportFaultExpr faultExpr) >>= (append "]")
        faultExpr >>=
        (append "step {") >>=
        (exportBehaviorDecl stepDecl.Behavior) >>=
        (append " }")

        
    let rec exportCompDecl (compDecl:CompDecl) : AstToStringStateFunction =
        (exportComp compDecl.Comp) >>= (newParagraph) >>=
        (foreachWithSep compDecl.Subs       exportCompDecl     (newParagraph) ) >>
        (foreachWithSep compDecl.Fields     exportFieldDecl    (newParagraph) ) >>=
        (foreachWithSep compDecl.Faults     exportFaultDecl    (newParagraph) ) >>=
        (foreachWithSep compDecl.ReqPorts   exportReqPortDecl  (newParagraph) ) >>=
        (foreachWithSep compDecl.ProvPorts  exportProvPortDecl (newParagraph) ) >>=
        (foreachWithSep compDecl.Bindings   exportBndDecl      (newParagraph) ) >>=
        (foreachWithSep compDecl.Steps      exportStepDecl     (newParagraph) )


    let exportModel (compDecl:CompDecl) : string =
        let stateAfterExport =
            exportCompDecl compDecl AstToStringState.initial
        stateAfterExport.ToString()
