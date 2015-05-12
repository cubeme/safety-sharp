﻿// The MIT License (MIT)
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
                    // After _one_ rewrite, we return. This makes analysis of the algorithm easier
                    // Sliding window: The function findAndPushAssignmentInBlock looks through a peephole
                    // if nothing has to be done on the peephole, peephole is shifted to the right
                    // Example:
                    //   Assume Stm1;Stm2;Stm3;Stm4;Stm5
                    //     1st Peephole: None;Stm1
                    //     2nd Peephole: Stm1;Stm2
                    //     3rd Peephole: Stm2;Stm3
                    //     4th Peephole: Stm3;Stm4
                    //     5th Peephole: Stm4;Stm5
                    //   Every Stm was at least one time peepholeRight
                    let rec findAndPushAssignmentInBlock (revAlreadyLookedAt:Stm list,peepholeLeft:Stm option,peepholeRight:Stm option)
                                                         (rightNextToPeephole:Stm list) : (Stm*bool) = 
                        let peepholeLeft = peepholeLeft
                        match (peepholeLeft,peepholeRight) with
                            | (Some(Stm.Write(leftSid,_var,leftExpr)),Some(Assert (rightSid,rightExpr))) ->
                                // push over Assertion. Adapt rightExpr
                                let pushCandidate=peepholeLeft.Value
                                let newAssertStm =
                                    let newAssertExpr = rightExpr.rewriteExpr_varToExpr  (_var,leftExpr)
                                    Stm.Assert(rightSid,newAssertExpr)
                                let newBlock =
                                    (revAlreadyLookedAt |> List.rev)
                                    @ [newAssertStm;pushCandidate]
                                    @ rightNextToPeephole
                                (Stm.Block(blockSid,newBlock),true)
                            | (Some(Stm.Write(leftSid,_var,leftExpr)),Some(Assume (rightSid,rightExpr))) ->
                                // push over Assumption. Adapt rightExpr
                                let pushCandidate=peepholeLeft.Value
                                let newAssumeStm =
                                    let newAssumeStmExpr = rightExpr.rewriteExpr_varToExpr  (_var,leftExpr)
                                    Stm.Assume(rightSid,newAssumeStmExpr)
                                let newBlock =
                                    (revAlreadyLookedAt |> List.rev)
                                    @ [newAssumeStm;pushCandidate]
                                    @ rightNextToPeephole
                                (Stm.Block(blockSid,newBlock),true)
                            | (Some(Stm.Write(leftSid,_var,leftExpr)),Some(Choice (rightSid,rightChoices))) ->
                                // push into Choice. (prepend to each of the rightChoices at the beginning)
                                let pushCandidate=peepholeLeft.Value
                                let createNewChoice (choice:Stm) =
                                    choice.prependStatements uniqueStatementIdGenerator [pushCandidate]
                                let newChoiceStm = Stm.Choice(rightSid,rightChoices |> List.map createNewChoice)
                                assert rightNextToPeephole.IsEmpty // in treeified Stmts there is nothing after stochastic
                                let newBlock = ((newChoiceStm::revAlreadyLookedAt) |> List.rev)
                                (Stm.Block(blockSid,newBlock),true)
                            | (Some(Stm.Write(leftSid,_var,leftExpr)),Some(Stochastic (rightSid,rightStochasticChoices))) ->
                                // push into Stochastic (prepend to each of the rightStochasticChoices at the beginning). Adapt choiceExprs.
                                let pushCandidate=peepholeLeft.Value
                                let createNewChoice (choiceExpr:Expr,choiceStm:Stm) =
                                    let newChoiceExpr = choiceExpr.rewriteExpr_varToExpr (_var,leftExpr)
                                    let newChoiceStm = choiceStm.prependStatements uniqueStatementIdGenerator [pushCandidate]
                                    (newChoiceExpr,newChoiceStm)
                                let newChoiceStm = Stm.Stochastic(rightSid,rightStochasticChoices |> List.map createNewChoice)
                                assert rightNextToPeephole.IsEmpty // in treeified Stmts there is nothing after stochastic
                                let newBlock = ((newChoiceStm::revAlreadyLookedAt) |> List.rev)
                                (Stm.Block(blockSid,newBlock),true)
                            | (peepholeLeft,Some(stmOfRightPeephole)) ->
                                // recursive cases (Stochastic or Choices)
                                let (newStmOfRightPeephole,changedSomething) = findAndPushAssignmentNotAtTheEnd stmOfRightPeephole
                                let stmOfPeepholeLeft = if peepholeLeft.IsSome then [peepholeLeft.Value] else []
                                if changedSomething then
                                    let newBlock =
                                        (revAlreadyLookedAt |> List.rev)
                                        @ stmOfPeepholeLeft @ [newStmOfRightPeephole]
                                        @ rightNextToPeephole
                                    (Stm.Block(blockSid,newBlock),true)
                                else if rightNextToPeephole.IsEmpty then
                                    //nothing changed at all, so return old statement
                                    (stm,false)
                                else
                                    // shift peephole to the right
                                    let nextRevAlreadyLookedAt = stmOfPeepholeLeft @ revAlreadyLookedAt
                                    let nextPeepholeRight = Some(rightNextToPeephole.Head)
                                    let nextPeepholeLeft = peepholeRight
                                    let nextRightNextToPeephole = rightNextToPeephole.Tail
                                    findAndPushAssignmentInBlock (nextRevAlreadyLookedAt,nextPeepholeLeft,nextPeepholeRight) nextRightNextToPeephole
                            | _ ->
                                (stm,false)
                    if statements.IsEmpty = false then
                        let firstPeepholeRight = Some(statements.Head)
                        let firstPeepholeLeft = None
                        let firstRightNextToPeephole = statements.Tail
                        findAndPushAssignmentInBlock ([],firstPeepholeLeft,firstPeepholeRight) firstRightNextToPeephole
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
    let phase3PullChoicesTowardsBeginning () : TsamWorkflowFunction<_,unit> = workflow {
        // We assume treeified form and all assignments at the end. Thus there are only
        // Asserts, Choices and Stochastics. After this algorithm has finished, all
        // choices are at the beginning.
        // A) We need to pull choices out of stochastic:
        // Example:
        //    stochastic {                   choice {
        //       p1 => {                        { 
        //          choice {                        stochastic {
        //              {Stm1}                          p1 => {Stm1}
        //              {Stm2}                          p2 => {Stm3}
        //          }                ===>               p3 => {Stm4}
        //       }                                  }
        //       p2 => {                        }
        //          Stm3                        { 
        //       }                                  stochastic {
        //       p3 => {                                p1 => {Stm2}
        //          Stm4                                p2 => {Stm3}
        //       }                                      p3 => {Stm4}
        //                                          }
        //                                      }
        //                                   }
        // Note: Choice may be first in Block or direct Child of Stochastic
        // B) We need to pull a choice towards beginning over an Assume or Assert.
        // Assume/Assert prepend each choice. Assertion may not be pulled left over a
        // choice.

        // Summary: Cases to treat:
        // * StmBlock1 { Stm... ; StmStochastic { StmBlock2 { StmChoice { } } } <--- Choice is first and only child in a Block
        // * StmBlock1 { Stm... ; StmStochastic {  StmChoice { } } <--- Choice is the direct child of a Stochastic
        // * In a Block:  StmX;StmAssume;StmChoice
        // * In a Block:  StmX;StmAssert;StmChoice

        let! state = getState ()
        let uniqueStatementIdGenerator = state.Pgm.UniqueStatementIdGenerator

        let rec findAndPullChoicesNotAtTheBeginning (stm:Stm) : (Stm*bool) = //returns true, if change occurred
            match stm with
                | Stm.Block (blockSid,statements:Stm list) ->
                    ()
                | Stm.Choice (sid,choices: Stm list) ->
                    // We assume a treeified version. Thus this Stm.Choice is at the end of a Block.
                    // Thus nothing happens after this Stm.Choice. Thus this Stm.Choice is independent
                    // from whatever happens after the choice. We do not alter or add anything after the
                    // Stm.Choice, we only manipulate things inside each of the choices. Thus we can
                    // manipulate the choices in parallel.
                    let (newChoices,somethingChanged) =
                        choices |> List.map findAndPullChoicesNotAtTheBeginning
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
                                                            let (newChoiceStm,somethingChanged) = findAndPullChoicesNotAtTheBeginning choiceStm
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
        
        let rec findAndPullChoicesNotAtTheBeginningUntilFixpoint (stm:Stm) =
            let (newStm,wasChanged) = findAndPullChoicesNotAtTheBeginning stm
            if wasChanged then
                findAndPullChoicesNotAtTheBeginningUntilFixpoint newStm
            else
                stm
                
        let! model = getTsamModel ()
        let allChoicesAtTheBeginningBody = findAndPullChoicesNotAtTheBeginningUntilFixpoint (model.Body)
        let allChoicesAtTheBeginningModel = 
            { model with
                Pgm.Body = allChoicesAtTheBeginningBody
            }
        do! updateTsamModel allChoicesAtTheBeginningModel
    }

    let phase4PushStochasticsTowardsEnd() : TsamWorkflowFunction<_,unit> = workflow {
        //Assertions/Assumptions. It may be pulled over a probabilistic.
        return ()
    }
        
    let phase5MergeChoicesAtTheBeginning () : TsamWorkflowFunction<_,unit> = workflow {
        // We need to merge choices with choices:
        // Example:
        //    choice {                             choice {
        //       { Stm1 }                             { Stm1 }
        //       { Stm2 }                             { Stm2 }
        //       {                                    { Stm3 }
        //           choice {            ===>         { Stm4 }
        //               {Stm3}                    }
        //               {Stm4}
        //           }
        //       }
        //    }
        return ()
    }

    let phase6MergeStochasticsAtTheEnd () : TsamWorkflowFunction<_,unit> = workflow {
        // We want Stochastic Statements to be exactly before the Assignment Statements
        // They should be there
        // We need to merge stochastics with stochastics:
        // Example:
        //    stochastic {                       stochastic {
        //       p1 => {Stm1}                       p1 => {Stm1}
        //       p2 => stochastic {                 p2 * p3 => {Stm3}
        //           p3 => {Stm3}                   p2 * p4 => {Stm4}
        //           p4 => {Stm4}     ===>          p2 * p5 => {Stm5} 
        //           p5 => {Stm5}                }
        //       }
        //    }
        return ()
    }

    let transformTsamToTsamInGuardToAssignmentForm () : TsamWorkflowFunction<_,unit> = workflow {
        // TODO: Assume Single Assignment Form        
        do! phase1TreeifyAndNormalize ()
        do! phase2PushAssignmentsNotAtTheEnd ()
        do! phase3PullChoicesTowardsBeginning ()
        do! phase4PushStochasticsTowardsEnd ()
        do! phase5MergeChoicesAtTheBeginning ()
        do! phase6MergeStochasticsAtTheEnd ()
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