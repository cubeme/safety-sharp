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

namespace SafetySharp.Models.Sam

open SafetySharp.Models.GenericAstWriter

module internal SamAstToString =

    //////////////////////////////////////////////////////////////////////////////
    // actual export
    //////////////////////////////////////////////////////////////////////////////
     
    let exportVar (var:Var) : AstToStringStateFunction =
        let toAppend =
            match var with
                | Var(str) -> str
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
            | Stm.Block (stmts) ->
                newLine >>= (append "{") >>= newLineAndIncreaseIndent >>= 
                (foreach stmts (fun stm -> exportStm stm >>= newLine)) >>=
                decreaseIndent >>= (append "}") >>= newLine
            | Stm.Choice (choices:Clause list) ->
                newLine >>= (append "choice {") >>= newLineAndIncreaseIndent >>= 
                (foreach choices (fun clause -> 
                                       exportExpr clause.Guard >>= append " => " >>= exportStm clause.Statement >>= newLine)
                                 ) >>=
                decreaseIndent >>= (append "}") >>= newLine
            | Stm.Write (var,expr) ->
                (exportVar var) >>=
                (append " := ") >>=
                (exportExpr expr) >>=
                (append "; ")
       
    let exportType (_type:Type) : AstToStringStateFunction =
        match _type with
            | BoolType -> append "bool"
            | IntType -> append "int"

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
        (foreachWithSep pgm.Globals exportGlobalVarDecl (newLine) ) >>=
        newParagraph >>=
        (foreachWithSep pgm.Locals  exportLocalVarDecl  (newParagraph) ) >>=
        newParagraph >>=
        (exportStm pgm.Body )


    let exportModel (pgm:Pgm) : string =
        let stateAfterExport =
            exportPgm pgm AstToStringState.initial
        stateAfterExport.ToString()


