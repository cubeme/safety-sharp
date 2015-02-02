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

namespace SafetySharp.Analysis.VerificationCondition

module internal SamModified =
    // Advantages:
    //  * Peekhole optimizations are easier.
    //  * Transformation to verification condition is slightly easier.
    // See
    //  * Cormac Flanagan, James Saxe. Avoiding Exponential Explosion: Generating Compact Verification Conditions. http://dx.doi.org/10.1145/360204.360220
    //  * Greg Nelson. A generalization of Dijkstra's calculus. http://dx.doi.org/10.1145/69558.69559

    type UOp = SafetySharp.Models.Sam.UOp
    type BOp = SafetySharp.Models.Sam.BOp
    type Var = SafetySharp.Models.Sam.Var
    type Val = SafetySharp.Models.Sam.Val
    type Expr = SafetySharp.Models.Sam.Expr
    
    type Stm =
        | Assert of Expression : Expr       //semantics: wp( Stm.Assert(e), phi) := e && phi (formula to prove is false, when assertion is false)
        | Assume of Expression : Expr       //semantics: wp( Stm.Assume(e), phi) := e -> phi
        | Block of Statements: Stm list
        | Choice of Choices : Stm list
        | Write of Variable:Var * Expression:Expr
    
    type Type = SafetySharp.Models.Sam.Type
    type GlobalVarDecl = SafetySharp.Models.Sam.GlobalVarDecl
    type LocalVarDecl = SafetySharp.Models.Sam.LocalVarDecl
 
    type Pgm = {
        Globals : GlobalVarDecl list
        Locals : LocalVarDecl list
        Body : Stm
    }

    let rec translateStm (stm : SafetySharp.Models.Sam.Stm) : Stm =
        match stm with
            | SafetySharp.Models.Sam.Stm.Block(statements) ->
                Stm.Block(statements |> List.map translateStm)
            | SafetySharp.Models.Sam.Stm.Choice (clauses) ->
                let translateClause ( clause :SafetySharp.Models.Sam.Clause) : Stm =
                    Stm.Block([Stm.Assume(clause.Guard);translateStm clause.Statement]) // the guard is now an assumption
                Stm.Choice(clauses |> List.map translateClause)
            | SafetySharp.Models.Sam.Stm.Write (variable,expression) ->
                Stm.Write (variable,expression)

    let translatePgm (pgm : SafetySharp.Models.Sam.Pgm ) : Pgm =
        {
            Pgm.Globals = pgm.Globals;
            Pgm.Locals = pgm.Locals;
            Pgm.Body = translateStm pgm.Body;
        }
                
    let rec createAndedExpr (exprs:Expr list) : Expr =
        if exprs.IsEmpty then
            Expr.Literal(Val.BoolVal(true)) //see Conjunctive Normal Form. If there is no clause, the formula is true.
        else if exprs.Tail = [] then
            // only one element, so return it
            exprs.Head
        else
            Expr.BExpr(exprs.Head,BOp.And,createAndedExpr exprs.Tail)
                
    let rec createOredExpr (exprs:Expr list) : Expr =
        if exprs.IsEmpty then
            Expr.Literal(Val.BoolVal(false)) //see Conjunctive Normal Form. An empty clause is unsatisfiable.
        else if exprs.Tail = [] then
            // only one element, so return it
            exprs.Head
        else
            Expr.BExpr(exprs.Head,BOp.Or,createOredExpr exprs.Tail)


module internal  WeakestPrecondition =
    open SamModified
    open SafetySharp.Models.SamHelpers
       
    let rec wp_rewriteExpr_varsToExpr (variable:Var,toExpr:Expr) (expr:Expr): Expr =
        match expr with
            | Expr.Literal (_val) -> Expr.Literal(_val)
            | Expr.Read (_var) -> if _var = variable then toExpr else expr
            | Expr.ReadOld (_var) -> expr //old variables keep their value
            | Expr.UExpr (expr,uop) -> Expr.UExpr(wp_rewriteExpr_varsToExpr (variable,toExpr) expr ,uop)
            | Expr.BExpr (left, bop, right) -> Expr.BExpr(wp_rewriteExpr_varsToExpr (variable,toExpr) left,bop,wp_rewriteExpr_varsToExpr (variable,toExpr) right)



    // formula is the formula which should be true after the execution
    let rec wp (stm:Stm) (formula:Expr) : Expr =
        match stm with
        | Assert (expr) ->
            Expr.BExpr(expr,BOp.And,formula)
        | Assume (expr) ->
            Expr.BExpr(expr,BOp.Implies,formula)
        | Block (statements) ->
            List.foldBack wp statements formula
        | Choice (choices) ->
            let choicesAsExpr =
                choices |> List.map (fun choice -> wp choice formula)
            Expr.createAndedExpr choicesAsExpr
        | Write (variable,expression) ->
            wp_rewriteExpr_varsToExpr (variable,expression) formula

