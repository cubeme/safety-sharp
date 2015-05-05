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

module internal VcGuardWithAssignmentModel =
    open SafetySharp.Models
    open SafetySharp.Models.SamHelpers
    
    type VarDecl = Tsam.GlobalVarDecl
    type Var = Tsam.Var
    type Val = Tsam.Val
    type BOp= Tsam.BOp
    type Expr = Tsam.Expr

    type Traceable = Tsam.Traceable

    // Predicate Transformers
    // Assume VcSam is in SSA-Form
    // Use Strongest Postcondition on the left side. Collect Guard...
    // Assumptions go on the left side
    // Forward derivation/ forward reasoning similar to strongest postcondition
    
    // The Proof ( a1 => b1 ) && ( a2 => b2 ) && ...   === ( a1 && b1 ) || ( a2 && b2 ) || ... in several cases:
    //   [Nafz12] Florian Nafz. Verhaltensgarantien in selbst-organisierenden Systemen.
    
    [<RequireQualifiedAccessAttribute>]
    type AtomicStm =
        | Assert of Expr
        | Assume of Expr
        | Write of Var * Expr
    
    type AtomicStmBlock =
        AtomicStmBlock of Statements:(AtomicStm list)
                static member concat (AtomicStmBlock(firstStmBlock)) (AtomicStmBlock(secondStmBlock)) : AtomicStmBlock =
                    AtomicStmBlock.AtomicStmBlock(firstStmBlock @ secondStmBlock)

    // number of paths is exponential in the number of nested choices
    let rec collectPaths (stm:Tsam.Stm) : AtomicStmBlock list =
        // Bottom up. Top down might be more efficient.
        match stm with
            | Tsam.Stm.Assert (_,expr) ->
                [AtomicStmBlock ([AtomicStm.Assert(expr)])]
            | Tsam.Stm.Assume (_,expr) ->
                [AtomicStmBlock ([AtomicStm.Assume(expr)])]
            | Tsam.Stm.Block (_,statements) ->
                let rec appendStatementOfBlock (previousStmBlocks:AtomicStmBlock list) (stm:Tsam.Stm) : AtomicStmBlock list =
                    // here we have to combine every possible path "previousStmBlocks X newStmBlocks"
                    // If one of the lists is empty, it should return the other list.
                    // Otherwise it would be possible, that the resulting combination list is empty.
                    let newStmBlocks = collectPaths stm
                    if previousStmBlocks.IsEmpty then
                        // Initially previousStmBlocks is empty. This could be omitted by using an empty
                        // StmBlock (AtomicStmBlock([]) as initial State for List.fold.
                        // Then previousStmBlocks should be empty by construction.
                        newStmBlocks
                    else if newStmBlocks.IsEmpty then
                        // Should not be empty by construction, but just to be sure
                        previousStmBlocks
                    else
                        // Combine                        
                        let combineWithEveryNewStmBlock (previousStmBlock:AtomicStmBlock) : AtomicStmBlock list =
                            newStmBlocks |> List.map (fun newStmBlock -> AtomicStmBlock.concat previousStmBlock newStmBlock)
                        previousStmBlocks |> List.collect combineWithEveryNewStmBlock
                statements |> List.fold appendStatementOfBlock []
            | Tsam.Stm.Choice (_,choices) ->
                choices |> List.collect collectPaths
            | Tsam.Stm.Stochastic (_,stochasticChoices) ->
                failwith "not supported"
            | Tsam.Stm.Write (_,variable,expression) ->
                [AtomicStmBlock ([AtomicStm.Write(variable,expression)])]

    
    let rec gwa_rewriteExpr_varsToExpr (currentValuation:Map<Var,Expr>) (expr:Expr) : Expr =
        match expr with
            | Expr.Literal (_) -> expr
            | Expr.Read (_var) ->                
                if currentValuation.ContainsKey _var then
                    currentValuation.Item _var
                else
                    expr
            | Expr.ReadOld (_var) -> expr //old variables keep their value
            | Expr.UExpr (expr,uop) ->
                Expr.UExpr (gwa_rewriteExpr_varsToExpr currentValuation expr,uop)
            | Expr.BExpr (left, bop, right) ->
                Expr.BExpr (gwa_rewriteExpr_varsToExpr currentValuation left, bop, gwa_rewriteExpr_varsToExpr currentValuation right)
        
    type GuardWithAssignments = {        
        Guard : Expr;
        Assignments : Map<Var,Expr>;
    }

    let transformAtomicStmBlockToGuardWithAssignments (globalVars:Var list) (AtomicStmBlock(toTransform)) : GuardWithAssignments =
        // Start with guard true. Every time we cross an assumption, we add this assumption to our guard.
        // Every time we cross an assignment, we update the current assignments (forward similar to strongest postcondition)
        let initialGuard =
            Expr.Literal(Val.BoolVal(true))
        let initialValuation =
            // add for each globalVar a self assignment. Local Vars should only appear during the statements.
            globalVars |> List.fold (fun (acc:Map<Var,Expr>) var -> acc.Add(var,Expr.Read(var))) Map.empty<Var,Expr>
        let foldStm (currentGuard:Expr,currentValuation:Map<Var,Expr>) (stm:AtomicStm) : Expr*Map<Var,Expr> =
            match stm with
                | AtomicStm.Assert (expr) ->
                    failwith "I am not sure yet, what to do with it. Have to read about strongest postcondition"
                    // I think, we could add the assertion, but it would generate a new proof obligation.
                | AtomicStm.Assume (expr) ->
                    let newExpr = gwa_rewriteExpr_varsToExpr currentValuation expr
                    let newGuard =
                        Expr.BExpr(currentGuard,BOp.And,newExpr)
                    (newGuard,currentValuation)
                | AtomicStm.Write (var, expr) ->
                    // replace vars in expr by their current valuation (such that no localVar occurs in any valuation)
                    let newExpr = gwa_rewriteExpr_varsToExpr currentValuation expr
                    let newValuation = currentValuation.Add(var,newExpr)
                    (currentGuard,newValuation)
        
        let finalGuard,finalValuation = toTransform |> List.fold foldStm (initialGuard,initialValuation)
        {
            GuardWithAssignments.Guard = finalGuard;
            GuardWithAssignments.Assignments = finalValuation;
        }
        
    let redirectFinalVarsAndRemoveNonFinalAssignments (nextGlobal : Map<Var,Var>) (gwa:GuardWithAssignments) =
        //finalVars:
        //   In SSA-Form each GlobalVar has several representatives with different versions of this variable
        //   after each assignment. The representative with the last version of each GlobalVar is in the set FinalVars        
        // remove every assignment entry, which is not done on a finalVar        
        let finalVars = nextGlobal |> Map.toList |> List.map (fun (original,final) -> final) |> Set.ofList      
        let nextGlobalToCurrent = nextGlobal |> Map.toList |> List.map (fun (oldVar,newVar) -> (newVar,oldVar) ) |> Map.ofList
        { gwa with
            GuardWithAssignments.Assignments =
                gwa.Assignments |> Map.filter (fun key value -> finalVars.Contains key)
                                |> Map.toList
                                |> List.map (fun (oldkey,value) -> (nextGlobalToCurrent.Item oldkey,value)) // use the nextGlobal redirection here
                                |> Map.ofList
        }


    type GuardWithAssignmentModel = {
        Globals : VarDecl list;
        GuardsWithFinalAssignments : GuardWithAssignments list;
    }

    // this is the main function of this algorithm
    let transformPgmToGuardWithFinalAssignmentModel (pgm:Tsam.Pgm) : GuardWithAssignmentModel =
        // SSA may not be necessary. Passive Form cannot be used with this algorithm.
        if pgm.CodeForm = Tsam.CodeForm.Passive then
            failwith "passive form cannot be used with this algorithm"
        let atomicStmBlocks = collectPaths pgm.Body
        let globalVars = pgm.Globals |> List.map (fun gl-> gl.Var)
        let guardsWithFinalAssignments =
            atomicStmBlocks |> List.map (transformAtomicStmBlockToGuardWithAssignments globalVars)
                            |> List.map (redirectFinalVarsAndRemoveNonFinalAssignments pgm.NextGlobal)
        {
            GuardWithAssignmentModel.Globals = pgm.Globals;
            GuardWithAssignmentModel.GuardsWithFinalAssignments = guardsWithFinalAssignments;
        }
        
    open SafetySharp.Workflow

        
    let transformWorkflow<'traceableOfOrigin> () : ExogenousWorkflowFunction<Tsam.Pgm,GuardWithAssignmentModel,'traceableOfOrigin,Tsam.Traceable,Traceable,unit> = workflow {
        let! model = getState ()
        let transformedModel = transformPgmToGuardWithFinalAssignmentModel model
        do! updateState transformedModel
    }