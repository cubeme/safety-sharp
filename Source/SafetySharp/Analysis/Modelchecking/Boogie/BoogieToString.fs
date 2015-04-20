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

namespace SafetySharp.Analysis.Modelchecking.Boogie

module internal BoogieToString =
    open SafetySharp.Models.SamToStringHelpers
    open BoogieSimplifiedAst

    //////////////////////////////////////////////////////////////////////////////
    // actual export
    //////////////////////////////////////////////////////////////////////////////
     
    let exportVar (var:Var) : AstToStringStateFunction =
        let toAppend =
            match var with
                | Var.Var(str) -> str
        append toAppend
       
       
    let exportUOp (uop:UOp) : AstToStringStateFunction =
        let toAppend =
            match uop with
                //| UOp.Minus -> "-"
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
                | BOp.Implies -> "->"
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
                | Val.BoolVal (_val) ->
                    match _val with
                        | true -> "true"
                        | false -> "false"
                | Val.NumbVal (_val) -> _val.ToString()
        append toAppend

    let rec exportExpr (expr:Expr) : AstToStringStateFunction =
        match expr with
            | Expr.Literal (_val) -> exportVal  _val
            | Expr.Read (_var) -> exportVar  _var
            | Expr.UExpr (expr,uop) ->                
                (exportUOp uop) >>= (append "(") >>= (exportExpr expr) >>= (append ")")
            | Expr.BExpr (exprLeft, bop, exprRight) ->
                (append "(") >>= (exportExpr exprLeft) >>= (append ")")  >>=
                (exportBOp bop) >>=
                (append "(") >>= (exportExpr exprRight) >>= (append ")") 

    let exportProcedureName (ProcedureName(name:string)) : AstToStringStateFunction =
        (append name)
       

    let rec exportStm (stm:Stm) : AstToStringStateFunction =
        match stm with
            | Stm.Assert (expr) ->
                (append "assert ") >>=
                (exportExpr expr) >>=
                (append "; ") >>= newLine
            | Stm.Assume (expr) ->
                (append "assume ") >>=
                (exportExpr expr) >>=
                (append "; ") >>= newLine
            | Stm.Write (var,expr) ->
                (exportVar var) >>=
                (append " := ") >>=
                (exportExpr expr) >>=
                (append ";") >>= newLine
            | Stm.Call (callee,exprs) ->
                (append "call ") >>=
                (exportProcedureName callee) >>=
                (append " ( ") >>=
                (foreachWithSep exprs exportExpr (append ",") ) >>=
                (append ") ;") >>= newLine
                
    let exportBlockId (BlockId(blockid:string)) =
        (append blockid)
            
    let exportTransfer (transfer:Transfer) : AstToStringStateFunction =
        match transfer with
            | Transfer.Goto (blockids) ->
                (append "goto ") >>=
                (foreachWithSep blockids exportBlockId (append ",") ) >>=
                (append ";")
            | Transfer.Return (optExpr) ->
                let appendParameter =
                    match optExpr with
                        | None -> (append "")
                        | Some (expr) -> 
                            (append " ") >>= (exportExpr expr)
                (append "return") >>=
                (appendParameter) >>=
                (append ";")
            
    let exportCodeBlock (codeBlock:CodeBlock) : AstToStringStateFunction =
        (exportBlockId codeBlock.BlockId) >>=
        (append ":") >>= newLineAndIncreaseIndent >>=
        (foreach codeBlock.Statements exportStm) >>=
        (exportTransfer codeBlock.Transfer) >>= newLineAndDecreaseIndent
    
    
    let exportType (_type:Type) : AstToStringStateFunction =
        match _type with
            | Type.BoolType -> append "bool"
            | Type.IntType -> append "int"

    let exportVarDecl (varDecl:VarDecl) : AstToStringStateFunction =
        (append "var") >>=
        (whitespace) >>=
        (exportVar varDecl.Var) >>=
        (append ": ") >>=
        (exportType varDecl.Type) >>=
        (append ";") >>= newLine
            
    let exportProcedure (procedure:Procedure) : AstToStringStateFunction =
        (append "procedure ") >>=
        (exportProcedureName procedure.ProcedureName) >>=
        (append "(") >>=
        (foreachWithSep procedure.InParameters exportVarDecl (append ",")) >>=
        (append ")") >>=
        (append " returns") >>=        
        (append "(") >>=
        (foreachWithSep procedure.OutParameters exportVarDecl (append ",")) >>=
        (append ")") >>= newLine >>=
        (append "    ") >>=
        (append "modifies ") >>=
        (foreachWithSep procedure.Modifies exportVar (append ",")) >>=
        (append ";") >>= newLine >>=
        (append "{") >>= newLineAndIncreaseIndent >>=
        (foreach procedure.LocalVars exportVarDecl ) >>=
        (foreach procedure.Blocks exportCodeBlock ) >>=
         newLineAndDecreaseIndent >>= (append "}") >>= newParagraph

    let rec exportPgm (pgm:Pgm) : AstToStringStateFunction =
        (foreach pgm.GlobalVars exportVarDecl) >>= newParagraph >>=
        (foreach pgm.Procedures exportProcedure)


    let exportModel (pgm:Pgm) : string =
        let stateAfterExport =
            exportPgm pgm AstToStringState.initial
        stateAfterExport.ToString()

    open SafetySharp.Workflow

    let boogieToStringWf<'traceableOfOrigin> () 
            : ExogenousWorkflowFunction<Pgm,string,'traceableOfOrigin,Traceable,Traceable,unit> = workflow {
        let! model = getState ()
        do! updateState (exportModel model)
    }
