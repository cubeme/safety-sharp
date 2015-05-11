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

// Assume Single Assignment Form (To allow sp on the final assignments)

// The idea here is to transform the Tsam to a form, which resembles the guard with assignment form.
//   1st: Treeify: A control flow may split and merge. Avoid the merging by duplicating the statements that happen after the merge.
//           Example:
//                     ┌─ 4 ─┐                      ┌─ 4 ─ 6
//           1 ─ 2 ─ 3 ┤     ├ 6    ===>  1 ─ 2 ─ 3 ┤   
//                     └─ 5 ─┘                      └─ 5 ─ 6
//   2nd: Push every assignment to the end
//   3rd: Push every stochastic statement before the assignments (or to end, if none exists). Merge stochastic statements
//   4th: Pull every choice to the beginning. Merge choices.
// TODO: Empty Blocks and nested blocks are difficult to treat. Maybe write a normalizer to facilitate this step.
// Result: Choice* of (Assume*, Prob of (Assign*)) <--- exactly what we want


module internal VcGuardWithAssignmentModel =
    open SafetySharp.Models
    open SafetySharp.Models.TsamHelpers
    
    type VarDecl = Tsam.GlobalVarDecl
    type Var = Tsam.Var
    type Val = Tsam.Val
    type BOp= Tsam.BOp
    type Expr = Tsam.Expr

    type Traceable = Tsam.Traceable

    open SafetySharp.Workflow
    open SafetySharp.Models.Tsam
    open SafetySharp.Models.TsamMutable

    let phase1TreeifyAndNormalize () : TsamWorkflowFunction<_,unit> = workflow {
        // Example:
        //           ┌─ 4 ─┐                      ┌─ 4 ─ 6
        // 1 ─ 2 ─ 3 ┤     ├ 6    ===>  1 ─ 2 ─ 3 ┤   
        //           └─ 5 ─┘                      └─ 5 ─ 6
        do! TsamMutable.treeifyStm ()
        do! TsamMutable.normalizeBlocks ()
    }

    let phase2PushAssignmentsNotAtTheEnd () : TsamWorkflowFunction<_,unit> = workflow {
        // We assume treeified form.
        let! state = getState ()
        let uniqueStatementIdGenerator = state.Pgm.UniqueStatementIdGenerator

        let rec findAndPushAssignmentNotAtTheEnd (stm:Stm) : (Stm*bool) = //returns true, if change occurred
            match stm with
                | Stm.Block (blockSid,statements:Stm list) ->
                    ///////////// Here we rewrite the block. Result must be block                    
                    // after _one_ rewrite, we return. This makes analysis of the algorithm easier                    
                    // at least two statements are necessary to analyze
                    // the function findAndPushAssignmentInBlock looks through a peephole (pushCandidate,pushAfter)
                    // if nothing has to be done on the peephole, peephole is shifted to the right
                    let rec findAndPushAssignmentInBlock (revAlreadyLookedAt:Stm list,pushCandidate:Stm,pushAfter:Stm)
                                                         (rightNextToPeephole:Stm list) : (Stm*bool) = 
                        match (pushCandidate,pushAfter) with
                            | (Stm.Write(leftSid,_var,leftExpr),Assert (rightSid,rightExpr)) ->
                                // push over Assertion
                                let newAssertStm =
                                    let newAssertExpr = rightExpr.rewriteExpr_varToExpr  (_var,leftExpr)
                                    Stm.Assert(rightSid,newAssertExpr)
                                let newBlock =
                                    (revAlreadyLookedAt |> List.rev)
                                    @ [newAssertStm;pushCandidate]
                                    @ rightNextToPeephole
                                (Stm.Block(blockSid,newBlock),true)
                            | (Stm.Write(leftSid,_var,leftExpr),Assume (rightSid,rightExpr)) ->
                                // push over Assumption
                                let newAssumeStm =
                                    let newAssumeStmExpr = rightExpr.rewriteExpr_varToExpr  (_var,leftExpr)
                                    Stm.Assume(rightSid,newAssumeStmExpr)
                                let newBlock =
                                    (revAlreadyLookedAt |> List.rev)
                                    @ [newAssumeStm;pushCandidate]
                                    @ rightNextToPeephole
                                (Stm.Block(blockSid,newBlock),true)
                            | (Stm.Write(leftSid,_var,leftExpr),Choice (rightSid,rightChoices)) ->
                                // push into Choice
                                let createNewChoice (choice:Stm) =
                                    choice.prependStatements uniqueStatementIdGenerator [pushCandidate]
                                let newChoiceStm = Stm.Choice(rightSid,rightChoices |> List.map createNewChoice)
                                assert rightNextToPeephole.IsEmpty // in treeified Stmts there is nothing after stochastic
                                let newBlock = ((newChoiceStm::revAlreadyLookedAt) |> List.rev)
                                (Stm.Block(blockSid,newBlock),true)
                            | (Stm.Write(leftSid,_var,leftExpr),Stochastic (rightSid,rightStochasticChoices)) ->
                                // push into Stochastic
                                let createNewChoice (choiceExpr:Expr,choiceStm:Stm) =
                                    let newChoiceExpr = choiceExpr.rewriteExpr_varToExpr (_var,leftExpr)
                                    let newChoiceStm = choiceStm.prependStatements uniqueStatementIdGenerator [pushCandidate]
                                    (newChoiceExpr,newChoiceStm)
                                let newChoiceStm = Stm.Stochastic(rightSid,rightStochasticChoices |> List.map createNewChoice)
                                assert rightNextToPeephole.IsEmpty // in treeified Stmts there is nothing after stochastic
                                let newBlock = ((newChoiceStm::revAlreadyLookedAt) |> List.rev)
                                (Stm.Block(blockSid,newBlock),true)
                            | _ -> 
                                // pushCandidate is not a Write or we do not have a rule how to push,
                                // so shift peephole to the right.
                                if rightNextToPeephole.IsEmpty then
                                    //nothing changed at all, so return old statement
                                    (stm,false)
                                else
                                    let nextRevAlreadyLookedAt = pushCandidate::revAlreadyLookedAt
                                    let nextPushCandidate = pushAfter
                                    let nextPushAfter = rightNextToPeephole.Head
                                    let nextRightNextToPeephole = rightNextToPeephole.Tail
                                    findAndPushAssignmentInBlock (nextRevAlreadyLookedAt,nextPushCandidate,nextPushAfter) nextRightNextToPeephole
                    if statements.Length >= 2 then
                        let firstPushCandidate = statements.Head
                        let firstPushAfter = statements.Tail.Head
                        let firstRightNextToPeephole = statements.Tail.Tail
                        findAndPushAssignmentInBlock ([],firstPushCandidate,firstPushAfter) firstRightNextToPeephole
                    else
                        (stm,false)
                    ///////////// End of rewriting Block
                | Stm.Choice (sid,choices: Stm list) ->
                    // We assume a treeified version. Thus this Stm.Choice is at the end of a Block.
                    // Thus nothing happens after this Stm.Choice. Thus this Stm.Choice is independent
                    // from whatever happens after the choice. We do not alter or add anything after the
                    // Stm.Choice, we only manipulate things inside each of the choices. Thus we can
                    // manipulate the choices in parallel.
                    let (newChoices,somethingChanged) =
                        choices |> List.map findAndPushAssignmentNotAtTheEnd
                                |> List.unzip
                    let somethingChanged = somethingChanged |> List.exists id
                    if somethingChanged then
                        (Stm.Choice(sid,newChoices),true)
                    else
                        (stm,false)
                | Stm.Stochastic (sid,stochasticChoice: (Expr*Stm) list) ->
                    // See Stm.Choice, why we can manipulate each stochasticChoice in parallel
                    let (newChoices,somethingChanged) =
                        stochasticChoice |> List.map (fun (choiceProb,choiceStm) ->
                                                            let (newChoiceStm,somethingChanged) = findAndPushAssignmentNotAtTheEnd choiceStm
                                                            ((choiceProb,newChoiceStm),somethingChanged)
                                                        )
                                            |> List.unzip
                    let somethingChanged = somethingChanged |> List.exists id
                    if somethingChanged then
                        (Stm.Stochastic(sid,newChoices),true)
                    else
                        (stm,false)
                | _ ->
                    (stm,false)
        
        let rec findAndPushAssignmentNotAtTheEndUntilFixpoint (stm:Stm) =
            let (newStm,wasChanged) = findAndPushAssignmentNotAtTheEnd stm
            if wasChanged then
                findAndPushAssignmentNotAtTheEndUntilFixpoint newStm
            else
                stm
                
        let! model = getTsamModel ()
        let allStatementsAtTheEndBody = findAndPushAssignmentNotAtTheEndUntilFixpoint (model.Body)
        let allStatementsAtTheEndModel = 
            { model with
                Pgm.Body = allStatementsAtTheEndBody
            }
        do! updateTsamModel allStatementsAtTheEndModel

    }

    let phase3PushStochasticsTowardsEnd () : TsamWorkflowFunction<_,unit> = workflow {
        return ()
    }

    let phase4PullChoicesTowardsBeginning () : TsamWorkflowFunction<_,unit> = workflow {
        return ()
    }

    let transformTsamToTsamInGuardToAssignmentForm () : TsamWorkflowFunction<_,unit> = workflow {
        // TODO: Assume Single Assignment Form
        
        do! (phase1TreeifyAndNormalize ())
        do! iterateToFixpoint (phase2PushAssignmentsNotAtTheEnd ())
        do! iterateToFixpoint (phase3PushStochasticsTowardsEnd ())
        do! iterateToFixpoint (phase4PullChoicesTowardsBeginning ())
        return ()
    }
    

    type GuardWithAssignments = {        
        Guard : Expr;
        Assignments : Map<Var,Expr>;
    }   
        
    type GuardWithAssignmentModel = {
        Globals : VarDecl list;
        GuardsWithFinalAssignments : GuardWithAssignments list;
    }
    
    let transformGwaTsamToGwaModel (pgm:Tsam.Pgm) : GuardWithAssignmentModel =
        {
            GuardWithAssignmentModel.Globals = [];
            GuardWithAssignmentModel.GuardsWithFinalAssignments = [];
        }

    open SafetySharp.ITracing

    type GuardWithAssignmentModelTracer<'traceableOfOrigin> = {
        GuardWithAssignmentModel : GuardWithAssignmentModel;
        TraceablesOfOrigin : 'traceableOfOrigin list;
        ForwardTracer : 'traceableOfOrigin -> Tsam.Traceable;
    }
        with
            interface ITracing<GuardWithAssignmentModel,'traceableOfOrigin,Tsam.Traceable,GuardWithAssignmentModelTracer<'traceableOfOrigin>> with
                member this.getModel = this.GuardWithAssignmentModel
                member this.getTraceablesOfOrigin : 'traceableOfOrigin list = this.TraceablesOfOrigin
                member this.setTraceablesOfOrigin (traceableOfOrigin:('traceableOfOrigin list)) = {this with TraceablesOfOrigin=traceableOfOrigin}
                member this.getForwardTracer : ('traceableOfOrigin -> Sam.Traceable) = this.ForwardTracer
                member this.setForwardTracer (forwardTracer:('traceableOfOrigin -> Sam.Traceable)) = {this with ForwardTracer=forwardTracer}
                member this.getTraceables : Tsam.Traceable list =
                    this.GuardWithAssignmentModel.Globals |> List.map (fun varDecl -> Traceable.Traceable(varDecl.Var))
                    
                    
    let transformWorkflow<'traceableOfOrigin> () : ExogenousWorkflowFunction<TsamMutable.MutablePgm<'traceableOfOrigin>,GuardWithAssignmentModelTracer<'traceableOfOrigin>> = workflow {
        do! transformTsamToTsamInGuardToAssignmentForm ()

        let! state = getState ()
        let model = state.Pgm
        let transformed =
            {
                GuardWithAssignmentModelTracer.GuardWithAssignmentModel = transformGwaTsamToGwaModel model;
                GuardWithAssignmentModelTracer.TraceablesOfOrigin = state.TraceablesOfOrigin;
                GuardWithAssignmentModelTracer.ForwardTracer = state.ForwardTracer;
            }
        do! updateState transformed
    }