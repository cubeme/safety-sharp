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

module internal VcGuardToAssignForm =
    open VcSam
    open SafetySharp.Models.SamHelpers
    
    // Predicate Transformers
    // Assume VcSam is in SSA-Form
    // Use Strongest Postcondition on the left side. Collect Guard...
    // Assumptions go on the left side
    // Forward derivation/ forward reasoning similar to strongest postcondition
    
    
    [<RequireQualifiedAccessAttribute>]
    type AtomicStm =
        | Assert of Expr
        | Assume of Expr
        | Write of Var * Expr
    
    type AtomicStmBlock =
        AtomicStmBlock of AtomicStm list //more Type safety
                static member concat (AtomicStmBlock(firstStmBlock)) (AtomicStmBlock(secondStmBlock)) : AtomicStmBlock =
                    AtomicStmBlock.AtomicStmBlock(firstStmBlock @ secondStmBlock)
                
            (*with
                static member concatMany (stmBlocks : AtomicStmBlock list) : AtomicStmBlock =
                    let rec concatHelper (concatenated:AtomicStm list) (toConcat:AtomicStmBlock list) : AtomicStmBlock =
                        if toConcat.IsEmpty then
                            AtomicStmBlock(concatenated)
                        else
                            match toConcat.Head with
                                | AtomicStmBlock(nextElements) ->
                                    concatHelper (concatenated @ nextElements ) toConcat.Tail
                    concatHelper [] stmBlocks
            *)


    // number of paths is exponential in the number of nested choices
    let rec collectPaths (stm:Stm) : AtomicStmBlock list =
        // Bottom up. Top down might be more efficient.
        match stm with
            | Stm.Assert (_,expr) ->
                [AtomicStmBlock ([AtomicStm.Assert(expr)])]
            | Stm.Assume (_,expr) ->
                [AtomicStmBlock ([AtomicStm.Assume(expr)])]
            | Stm.Block (_,statements) ->
                let rec appendStatementOfBlock (previousStmBlocks:AtomicStmBlock list) (stm:Stm) : AtomicStmBlock list =
                    // here we have to combine every possible path "previousStmBlocks X newStmBlocks"
                    // If one of the lists is empty, it should return the other list.
                    // Otherwise it would be possible, that the resulting combination list is empty.
                    let newStmBlocks = collectPaths stm
                    if previousStmBlocks.IsEmpty then
                        newStmBlocks
                    else if newStmBlocks.IsEmpty then
                        previousStmBlocks
                    else
                        // combine                        
                        let combineWithEveryNewStmBlock (previousStmBlock:AtomicStmBlock) : AtomicStmBlock list =
                            newStmBlocks |> List.map (fun newStmBlock -> AtomicStmBlock.concat previousStmBlock newStmBlock)
                        previousStmBlocks |> List.collect combineWithEveryNewStmBlock
                statements |> List.fold appendStatementOfBlock []
            | Stm.Choice (_,choices) ->
                choices |> List.collect collectPaths
            | Stm.Write (_,variable,expression) ->
                [AtomicStmBlock ([AtomicStm.Write(variable,expression)])]

    type GuardWithAssignments = {
        GuardOfCurrentBranch : Expr;
        AssignmentsUntilStm : (Stm*Expr) list;
    }

    let transformAtomicStmsToGuardWithAssignments (finalVars:Set<Var>) = []

        //links werden guards gesammelt. Dies wird durch strongest Postcondition gemacht
        //rechts kommen die zuweisungen. Wir wissen, dass es die richtige Zuweisung ist, wenn es der letzte wert ist, der geschrieben wird.

        //finalVars:
        //  In SSA-Form each GlobalVar has several representatives with different versions of this variable
        //  after each assignment. The representative with the last version of each GlobalVar is in the set FinalVars

    (*       
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
        | Assert (_,expr) ->
            Expr.BExpr(expr,BOp.And,formula)
        | Assume (_,expr) ->
            Expr.BExpr(expr,BOp.Implies,formula)
        | Block (_,statements) ->
            List.foldBack wp statements formula
        | Choice (_,choices) ->
            let choicesAsExpr =
                choices |> List.map (fun choice -> wp choice formula)
            Expr.createAndedExpr choicesAsExpr
        | Write (_,variable,expression) ->
            wp_rewriteExpr_varsToExpr (variable,expression) 
    *)