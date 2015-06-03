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


module internal TsamToString =
    open SafetySharp.Models.SamToStringHelpers
    open Tsam
    
    let realFormat = new System.Globalization.CultureInfo("en-US")

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
         
    let exportStatementId (sid:StatementId) : AstToStringStateFunction =
        let toAppend =
            match sid with | StatementId.StatementId(id) -> sprintf "%d" id
        append toAppend

    let exportVal (_val:Val) : AstToStringStateFunction =
        let toAppend =
            match _val with
                | Val.BoolVal (_val) ->
                    match _val with
                        | true -> "true"
                        | false -> "false"
                | Val.NumbVal (_val) -> _val.ToString()
                | Val.RealVal (_val) -> System.Convert.ToString(_val,realFormat)
                | Val.ProbVal (_val) -> System.Convert.ToString(_val,realFormat)
        append toAppend

    let rec exportExpr (expr:Expr) : AstToStringStateFunction =
        match expr with
            | Expr.Literal (_val) -> exportVal  _val
            | Expr.Read (_var) -> exportVar  _var
            | Expr.ReadOld (_var) -> (append "prev(") >>= (exportVar _var) >>= (append ")")
            | Expr.UExpr (expr,uop) ->                
                //sprintf "%s(%s)" (exportUOp state uop)  (exportExpr state expr)
                (exportUOp uop) >>= (append "(") >>= (exportExpr expr) >>= (append ")")
            | Expr.BExpr (exprLeft, bop, exprRight) ->
                (append "(") >>= (exportExpr exprLeft) >>= (append ")")  >>=
                (exportBOp bop) >>=
                (append "(") >>= (exportExpr exprRight) >>= (append ")") 
       
    let rec exportStm (stm:Stm) : AstToStringStateFunction =
        match stm with
            | Stm.Assert (sid,expr) ->
                (append "assert ") >>=
                (exportExpr expr) >>=
                (append "; ") >>=
                (append "\t\t\t// ") >>= (exportStatementId sid) >>= newLine
            | Stm.Assume (sid,expr) ->
                (append "assume ") >>=
                (exportExpr expr) >>=
                (append "; ") >>=
                (append "\t\t\t// ") >>= (exportStatementId sid) >>= newLine
            | Stm.Block (sid,stmts) ->
                newLine >>= (append "{") >>= newLineAndIncreaseIndent >>= 
                (foreach stmts (fun stm -> exportStm stm >>= newLine)) >>=
                decreaseIndent >>= (append "}") >>=
                (append "\t\t\t// ") >>= (exportStatementId sid) >>= newLine
            | Stm.Choice (sid,choices:Stm list) ->
                newLine >>= (append "choice {") >>= newLineAndIncreaseIndent >>= 
                (foreach choices exportStm) >>=
                decreaseIndent >>= (append "}") >>=
                (append "\t\t\t// ") >>= (exportStatementId sid) >>= newLine
            | Stm.Stochastic (sid,stochasticChoices) ->
                newLine >>= (append "stochastic {") >>= newLineAndIncreaseIndent >>= 
                (foreach stochasticChoices
                    (fun (probExpr,stm) -> 
                        exportExpr probExpr >>= append " => " >>= exportStm stm >>= newLine)
                    ) >>=
                decreaseIndent >>= (append "}") >>=
                (append "\t\t\t// ") >>= (exportStatementId sid) >>= newLine
            | Stm.Write (sid,var,expr) ->
                (exportVar var) >>=
                (append " := ") >>=
                (exportExpr expr) >>=
                (append "; ") >>=
                (append "\t\t\t// ") >>= (exportStatementId sid) >>= newLine
       
    let exportType (_type:Type) : AstToStringStateFunction =
        let onOverrun _overflow = 
            match _overflow with
                | OverflowBehavior.Error -> "error"
                | OverflowBehavior.WrapAround -> "wrap around"
                | OverflowBehavior.Clamp -> "clamp"
                | _ -> failwith "NotImplementedYet"
        match _type with
            | Type.BoolType -> append "bool"
            | Type.IntType -> append "int"
            | Type.RealType -> append "real"
            | Type.RangedIntType(_from,_to,_overflow) ->
                let newType = sprintf "int<%d..%d,%s on overrun>" _from _to (onOverrun _overflow)
                append newType
            | Type.RangedRealType(_from,_to,_overflow) ->
                //https://msdn.microsoft.com/en-us/library/ee370560.aspx
                let newType = sprintf "real<%s..%s,%s on overrun>" (System.Convert.ToString(_from,realFormat)) (System.Convert.ToString(_to,realFormat)) (onOverrun _overflow)
                append newType

    let exportLocalVarDecl (varDecl:LocalVarDecl) : AstToStringStateFunction =
        (exportType varDecl.Type) >>=
        (whitespace) >>=
        (exportVar varDecl.Var) >>=
        (append ";") >>= newLine

    let exportGlobalVarDecl (varDecl:GlobalVarDecl): AstToStringStateFunction =
        (exportType varDecl.Type) >>=
        (whitespace) >>=
        (exportVar varDecl.Var) >>=
        (whitespace) >>=
        (foreachWithSep varDecl.Init exportVal (append ",") ) >>=
        (append ";")
    
        
    let rec exportPgm (pgm:Pgm) : AstToStringStateFunction =
        (append "globals {") >>= (newLineAndIncreaseIndent) >>=
        (foreachWithSep pgm.Globals exportGlobalVarDecl (newLine) ) >>=
        (newLineAndDecreaseIndent) >>= (append "}") >>= newParagraph >>=
        (append "locals {") >>= (newLineAndIncreaseIndent) >>=
        (foreachWithSep pgm.Locals  exportLocalVarDecl  (newParagraph) ) >>=
        (newLineAndDecreaseIndent) >>= (append "}") >>= newParagraph >>=
        (exportStm pgm.Body )


    let exportModel (pgm:Pgm) : string =
        let stateAfterExport =
            exportPgm pgm AstToStringState.initial
        stateAfterExport.ToString()

    open SafetySharp.Workflow

    let exportModelWorkflow () 
            : ExogenousWorkflowFunction<TsamMutable.MutablePgm<'traceableOfOrigin>,string> = workflow {
        let! pgm = getState ()
        let asString = exportModel (pgm.Pgm)
        do! updateState asString
    }
    
    let texFilePackagesInHeader = """
\usepackage{listings}
\lstset{
	frame=single,
	breaklines=true
}
"""