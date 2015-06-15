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
//   2nd: Push every assignment to the very end
//   3rd: Pull every choice to the very beginning
//   4th: Push Assertions and Assumptions towards the beginning after the choices (Indirectly push every stochastic statement before the assignments (or to end, if none exists))
//   5th: Merge choices.
//   6th: Merge stochastic statements

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
        do! TsamMutable.unnestBlocks ()
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
                    // phase4PullAssertionsAndAssumptionsTowardsBeginning shows a single Statement peephole
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
                                let createNewChoice (choiceExpr:Expr option,choiceStm:Stm) =
                                    let newChoiceExpr =
                                        match choiceExpr with
                                            | Some(choiceExpr) -> Some (choiceExpr.rewriteExpr_varToExpr (_var,leftExpr))
                                            | None -> None
                                    let newChoiceStm = choiceStm.prependStatements uniqueStatementIdGenerator [pushCandidate]
                                    (newChoiceExpr,newChoiceStm)
                                let newChoiceStm = Stm.Choice(rightSid,rightChoices |> List.map createNewChoice)
                                assert rightNextToPeephole.IsEmpty // in treeified Stmts there is nothing after stochastic
                                let newBlock = ((newChoiceStm::revAlreadyLookedAt) |> List.rev)
                                (Stm.Block(blockSid,newBlock),true)
                            | (Some(Stm.Write(leftSid,_var,leftExpr)),Some(Stochastic (rightSid,rightStochasticChoices))) ->
                                // push into Stochastic (prepend to each of the rightStochasticChoices at the beginning). Adapt choiceExprs.
                                let pushCandidate=peepholeLeft.Value
                                let createNewChoice (choiceGuard:Expr,choiceStm:Stm) =
                                    let newChoiceGuard = choiceGuard.rewriteExpr_varToExpr (_var,leftExpr)
                                    let newChoiceStm = choiceStm.prependStatements uniqueStatementIdGenerator [pushCandidate]
                                    (newChoiceGuard,newChoiceStm)
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
                | Stm.Choice (sid,choices: (Expr option * Stm) list) ->
                    // We assume a treeified version. Thus this Stm.Choice is at the end of a Block.
                    // Thus nothing happens after this Stm.Choice. Thus this Stm.Choice is independent
                    // from whatever happens after the choice. We do not alter or add anything after the
                    // Stm.Choice, we only manipulate things inside each of the choices. Thus we can
                    // manipulate the choices in parallel.
                    let (newChoices,somethingChanged) =
                        choices |> List.map (fun (choiceGuard,choiceStm) ->
                                                            let (newChoiceStm,somethingChanged) = findAndPushAssignmentNotAtTheEnd choiceStm
                                                            ((choiceGuard,newChoiceStm),somethingChanged)
                                                        )
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
        // * 1) StmBlock1 { Stm... ; StmStochastic { StmBlock2 { StmChoice { } } } <--- Choice is first and only child in a Block
        // * 2) StmBlock1 { Stm... ; StmStochastic {  StmChoice { } } <--- Choice is the direct child of a Stochastic
        // * 3) In a Block:  StmX;StmAssume;StmChoice   => StmX;StmChoice (assume is part of choice)
        // * 4) In a Block:  StmX;StmAssert;StmChoice    => StmX;StmChoice (assert is part of choice)
        
        let! state = getState ()
        let uniqueStatementIdGenerator = state.Pgm.UniqueStatementIdGenerator

        let rec findAndPullChoicesNotAtTheBeginning (stm:Stm) : (Stm*bool) = //returns true, if change occurred
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
                    let rec traverseBlock (revAlreadyLookedAt:Stm list,peepholeLeft:Stm option,peepholeRight:Stm option)
                                                         (rightNextToPeephole:Stm list) : (Stm*bool) = 
                        let peepholeLeft = peepholeLeft
                        match (peepholeLeft,peepholeRight) with
                            | (Some(Assume (leftSid,leftExpr)),Some(Choice (rightSid,rightChoices)))
                                // case 3) In a Block:  StmX;StmAssume;StmChoice
                            | (Some(Assert (leftSid,leftExpr)),Some(Choice (rightSid,rightChoices))) ->
                                // case 4) In a Block:  StmX;StmAssert;StmChoice
                                // push into Choice. (prepend to each of the rightChoices at the beginning)
                                let pushCandidate=peepholeLeft.Value
                                let createNewChoice (choiceGuard:Expr option,choiceStm:Stm) =
                                    (choiceGuard,choiceStm.prependStatements uniqueStatementIdGenerator [pushCandidate])
                                let newChoiceStm = Stm.Choice(rightSid,rightChoices |> List.map createNewChoice)
                                assert rightNextToPeephole.IsEmpty // in treeified Stmts there is nothing after stochastic
                                let newBlock = ((newChoiceStm::revAlreadyLookedAt) |> List.rev)
                                (Stm.Block(blockSid,newBlock),true)
                            | (peepholeLeft,Some(stmOfRightPeephole)) ->
                                // recursive cases (Stochastic or Choices)
                                let (newStmOfRightPeephole,changedSomething) = findAndPullChoicesNotAtTheBeginning stmOfRightPeephole
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
                                    traverseBlock (nextRevAlreadyLookedAt,nextPeepholeLeft,nextPeepholeRight) nextRightNextToPeephole
                            | _ ->
                                (stm,false)
                    if statements.IsEmpty = false then
                        let firstPeepholeRight = Some(statements.Head)
                        let firstPeepholeLeft = None
                        let firstRightNextToPeephole = statements.Tail
                        traverseBlock ([],firstPeepholeLeft,firstPeepholeRight) firstRightNextToPeephole
                    else
                        (stm,false)
                    ///////////// End of rewriting Block
                | Stm.Choice (sid,choices: (Expr option*Stm) list) ->
                    // We assume a treeified version. Thus this Stm.Choice is at the end of a Block.
                    // Thus nothing happens after this Stm.Choice. Thus this Stm.Choice is independent
                    // from whatever happens after the choice. We do not alter or add anything after the
                    // Stm.Choice, we only manipulate things inside each of the choices. Thus we can
                    // manipulate the choices in parallel.
                    let (newChoices,somethingChanged) =
                        choices |> List.map (fun (choiceGuard,choiceStm) ->
                                                    let newChoiceStm,somethingChanged= findAndPullChoicesNotAtTheBeginning choiceStm
                                                    ((choiceGuard,newChoiceStm),somethingChanged)
                                            )
                                |> List.unzip
                    let somethingChanged = somethingChanged |> List.exists id
                    if somethingChanged then
                        (Stm.Choice(sid,newChoices),true)
                    else
                        (stm,false)
                | Stm.Stochastic (stochasticSid,stochasticChoices: (Expr*Stm) list) ->                    
                    // case 1) StmBlock1 { Stm... ; StmStochastic { StmBlock2 { StmChoice { } } } <--- Choice is first and only child in a Block
                    // case 2) StmBlock1 { Stm... ; StmStochastic {  StmChoice { } } <--- Choice is the direct child of a Stochastic
                    let rec traverseStochasticChoices (revAlreadyTraversed:(Expr*Stm) list) (toTraverse:(Expr*Stm) list) : (Stm*bool) = 
                            if toTraverse.IsEmpty then
                                (stm,false)
                            else
                                let (stochasticChoiceToTraverseExpr,stochasticChoiceToTraverseStm) = toTraverse.Head
                                match stochasticChoiceToTraverseStm with
                                    | Stm.Block(_,Stm.Choice(choiceToPullSid,choiceToPullChoices)::[] )
                                        //case 1: ... { StmBlock2 { StmChoice { } }
                                    | Stm.Choice(choiceToPullSid,choiceToPullChoices) ->
                                        //case 2: ... { StmChoice { } }
                                        let otherStochasticChoicesLeft = revAlreadyTraversed |> List.rev
                                        let otherStochasticChoicesRight = toTraverse.Tail
                                        let createChoice (choiceInStochasticGuard:Expr option, choiceInStochasticStm:Stm) : Expr option*Stm =
                                            // stochasticChoiceInTheMiddle contained the Stm.Choice. Only stochasticChoiceInTheMiddle is changed. See above.
                                            let stochasticChoiceInTheMiddle = (stochasticChoiceToTraverseExpr,choiceInStochasticStm)
                                            let stochasticChoicesInChoice = otherStochasticChoicesLeft@[stochasticChoiceInTheMiddle]@otherStochasticChoicesRight
                                            let stochasticChoiceStm = Stm.Stochastic(stochasticSid,stochasticChoicesInChoice)
                                            (choiceInStochasticGuard,stochasticChoiceStm.recursiveRenumberStatements uniqueStatementIdGenerator)
                                        let outerChoices = choiceToPullChoices |> List.map createChoice
                                        (Stm.Choice(choiceToPullSid,outerChoices),true)
                                    | _ ->
                                        // recursive case (try to change something inside)
                                        let (traversedStochasticChoice,somethingChanged) = findAndPullChoicesNotAtTheBeginning stochasticChoiceToTraverseStm
                                        if somethingChanged then
                                            let newChoices =
                                                (revAlreadyTraversed |> List.rev)
                                                @ [(stochasticChoiceToTraverseExpr,traversedStochasticChoice)]
                                                @ toTraverse.Tail
                                            (Stm.Stochastic (stochasticSid,newChoices),true)
                                        else
                                            //nothing was changed by toTraverse.Head, so try the next candidate in the list
                                            traverseStochasticChoices ((stochasticChoiceToTraverseExpr,stochasticChoiceToTraverseStm)::revAlreadyTraversed) (toTraverse.Tail)
                    traverseStochasticChoices [] stochasticChoices
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

    let phase4PullAssertionsAndAssumptionsTowardsBeginning() : TsamWorkflowFunction<_,unit> = workflow {
        //Assertions/Assumptions. It may be pulled over a probabilistic.
        
        let! state = getState ()
        let uniqueStatementIdGenerator = state.Pgm.UniqueStatementIdGenerator

        let rec findAndPull (stm:Stm) : (Stm*(Stm option)*bool) = //returns Stm (without pulled) * Stm to pull (if Stm to pull exists) * changedSomething
            match stm with
                | Stm.Block (blockSid,statements:Stm list) ->
                    ///////////// Here we rewrite the block. Result must be block                    
                    // After _one_ rewrite, we return. This makes analysis of the algorithm easier
                    // Sliding window: The function findAndPushAssignmentInBlock looks through a peephole
                    // if nothing has to be done on the peephole, peephole is shifted to the right
                    // Example:
                    //   Assume Stm1;Stm2;Stm3;Stm4;Stm5
                    //     1st Peephole: Stm1
                    //     2nd Peephole: Stm2
                    //     3rd Peephole: Stm3
                    //     4th Peephole: Stm4
                    //     5th Peephole: Stm5
                    //   Every Stm was at least one time peephole
                    let rec traverseBlock (revAlreadyLookedAt:Stm list,peephole:Stm)
                                                         (rightNextToPeephole:Stm list) : (Stm*(Stm option)*bool) = 
                        // recursive cases (Stochastic or Choices)
                        let (newStmOfPeephole,statementToPull,changedSomething) = findAndPull peephole
                        if changedSomething then
                            let statementToPull = if statementToPull.IsSome then [statementToPull.Value] else []
                            let newBlock =
                                (revAlreadyLookedAt |> List.rev)
                                @ statementToPull @ [newStmOfPeephole]
                                @ rightNextToPeephole
                            (Stm.Block(blockSid,newBlock),None,true)
                        else if rightNextToPeephole.IsEmpty then
                            //nothing changed at all, so return old statement
                            (stm,None,false)
                        else
                            // shift peephole to the right
                            let nextRevAlreadyLookedAt = peephole :: revAlreadyLookedAt
                            let nextPeephole = rightNextToPeephole.Head
                            let nextRightNextToPeephole = rightNextToPeephole.Tail
                            traverseBlock (nextRevAlreadyLookedAt,nextPeephole) nextRightNextToPeephole
                    if statements.IsEmpty = false then
                        let firstPeephole = statements.Head
                        let firstRightNextToPeephole = statements.Tail
                        traverseBlock ([],firstPeephole) firstRightNextToPeephole
                    else
                        (stm,None,false)
                    ///////////// End of rewriting Block
                | Stm.Choice (sid,choices: (Expr option*Stm) list) ->
                    // We assume a treeified version. Thus this Stm.Choice is at the end of a Block.
                    // Thus nothing happens after this Stm.Choice. Thus this Stm.Choice is independent
                    // from whatever happens after the choice. We do not alter or add anything after the
                    // Stm.Choice, we only manipulate things inside each of the choices. Thus we can
                    // manipulate the choices in parallel.
                    // We do not pull an assume/assert before a choice, but we could pull statements of a choice as
                    // first elements of each choice
                    let pullInChoice (choiceGuard,choiceStm) =
                        let newChoiceStm,statementToPull,somethingChanged = findAndPull choiceStm
                        if somethingChanged then
                            if statementToPull.IsSome then
                                let newId = uniqueStatementIdGenerator()
                                ((choiceGuard,Stm.Block(newId,statementToPull.Value::[newChoiceStm])),true)
                            else
                                ((choiceGuard,choiceStm),true)
                        else
                            ((choiceGuard,choiceStm),false)
                    let (newChoices,somethingChanged) =
                        choices |> List.map pullInChoice
                                |> List.unzip                                
                    let somethingChanged = somethingChanged |> List.exists id
                    if somethingChanged then
                        (stm,None,false)
                    else
                        let newChoiceStm = Stm.Choice(sid,newChoices)
                        (newChoiceStm,None,true)

                | Stm.Stochastic (stochasticSid,stochasticChoices: (Expr*Stm) list) ->
                    let rec traverseStochasticChoices (revAlreadyTraversed:(Expr*Stm) list) (toTraverse:(Expr*Stm) list) : (Stm*(Stm option)*bool) = 
                        if toTraverse.IsEmpty then
                            (stm,None,false)
                        else
                            let (stochasticChoiceToTraverseExpr,stochasticChoiceToTraverseStm) = toTraverse.Head
                            match stochasticChoiceToTraverseStm with
                                | Stm.Block(blockSid,Stm.Assert(assertToPullSid,assertToPullExpr)::otherBlockStmnts ) ->
                                    //case 1: ... { StmBlock2 { StmAssert { } }
                                    let newStochasticWithoutAssert : Stm =
                                        let otherStochasticChoicesLeft = revAlreadyTraversed |> List.rev
                                        let otherStochasticChoicesRight = toTraverse.Tail
                                        let stochasticChoiceInTheMiddle = (stochasticChoiceToTraverseExpr,Stm.Block(blockSid,otherBlockStmnts))
                                        let stochasticChoicesInChoice = otherStochasticChoicesLeft@[stochasticChoiceInTheMiddle]@otherStochasticChoicesRight
                                        let stochasticChoiceStm = Stm.Stochastic(stochasticSid,stochasticChoicesInChoice)
                                        stochasticChoiceStm
                                    let toPull = Stm.Assert(assertToPullSid,assertToPullExpr)
                                    (newStochasticWithoutAssert,Some(toPull),true)
                                | Stm.Block(blockSid,Stm.Assume(assumeToPullSid,assumeToPullExpr)::otherBlockStmnts ) ->
                                    //case 2: ... { StmBlock2 { StmAssume { } }
                                    let newStochasticWithoutAssume : Stm =
                                        let otherStochasticChoicesLeft = revAlreadyTraversed |> List.rev
                                        let otherStochasticChoicesRight = toTraverse.Tail
                                        let stochasticChoiceInTheMiddle = (stochasticChoiceToTraverseExpr,Stm.Block(blockSid,otherBlockStmnts))
                                        let stochasticChoicesInChoice = otherStochasticChoicesLeft@[stochasticChoiceInTheMiddle]@otherStochasticChoicesRight
                                        let stochasticChoiceStm = Stm.Stochastic(stochasticSid,stochasticChoicesInChoice)
                                        stochasticChoiceStm
                                    let toPull = Stm.Assume(assumeToPullSid,assumeToPullExpr)
                                    (newStochasticWithoutAssume,Some(toPull),true)
                                | Stm.Assert(assertToPullSid,assertToPullExpr) ->
                                    //case 3: ... { StmAssert { } }
                                    // generate block to be able to use case 1
                                    let newId = uniqueStatementIdGenerator()
                                    let assertInBlock = Stm.Assert(assertToPullSid,assertToPullExpr)
                                    let newBlock = Stm.Block(newId,[assertInBlock])
                                    (newBlock,None,true)
                                | Stm.Assume(assumeToPullSid,assumeToPullExpr) ->
                                    //case 4: ... { StmAssume { } }
                                    // generate block to be able to use case 2
                                    let newId = uniqueStatementIdGenerator()
                                    let assumeInBlock = Stm.Assume(assumeToPullSid,assumeToPullExpr)
                                    let newBlock = Stm.Block(newId,[assumeInBlock])
                                    (newBlock,None,true)
                                | _ ->
                                    // recursive case (try to change something inside)
                                    // stochastic statement may propagate upwards
                                    let (traversedStochasticChoice,statementToPull,somethingChanged) = findAndPull stochasticChoiceToTraverseStm
                                    if somethingChanged then
                                        let newChoices =
                                            (revAlreadyTraversed |> List.rev)
                                            @ [(stochasticChoiceToTraverseExpr,traversedStochasticChoice)]
                                            @ toTraverse.Tail
                                        let stochasticStatement = Stm.Stochastic (stochasticSid,newChoices)
                                        (stochasticStatement,statementToPull,true)
                                    else
                                        //nothing was changed by toTraverse.Head, so try the next candidate in the list
                                        traverseStochasticChoices ((stochasticChoiceToTraverseExpr,stochasticChoiceToTraverseStm)::revAlreadyTraversed) (toTraverse.Tail)
                    traverseStochasticChoices [] stochasticChoices
                | _ ->
                    (stm,None,false)
        
        let rec findAndPullUntilFixpoint (stm:Stm) =
            let (newStm,statementToPull,wasChanged) = findAndPull stm
            if wasChanged then
                let newStm =
                    if statementToPull.IsSome then
                        let newId = uniqueStatementIdGenerator()
                        Stm.Block(newId,[statementToPull.Value;newStm])
                    else
                        newStm
                findAndPullUntilFixpoint newStm
            else
                stm
                
        let! model = getTsamModel ()
        let allAssumptionsAndAssertionsAfterChoiceBody = findAndPullUntilFixpoint (model.Body)
        let allAssumptionsAndAssertionsAfterChoiceModel = 
            { model with
                Pgm.Body = allAssumptionsAndAssertionsAfterChoiceBody
            }
        do! updateTsamModel allAssumptionsAndAssertionsAfterChoiceModel
    }
        
    let phase5MergeChoicesAtTheBeginning () : TsamWorkflowFunction<_,unit> = workflow {
        // We need to merge choices with choices:
        // Example 1:
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
        // Example 2:
        //    choice {                                        choice {
        //       guard1  => { Stm1 }                             guard1             => { Stm1 }
        //       ---     => { Stm2 }                             ---                => { Stm2 }
        //       guard34 => {                                    guard34 && guard3  => { Stm3 }
        //                      choice {            ===>         guard34            => { Stm4 }
        //                         guard3 => {Stm3}          }
        //                         ---    => {Stm4}
        //                      }
        //       }
        //    }
        
        let! state = getState ()
        let uniqueStatementIdGenerator = state.Pgm.UniqueStatementIdGenerator
        let rec findAndMerge (stm:Stm) : (Stm*bool) = //returns Stm (without pulled) * Stm to pull (if Stm to pull exists) * changedSomething
            match stm with
                | Stm.Block (blockSid,statements:Stm list) ->
                    ///////////// Here we rewrite the block. Result must be block                    
                    // After _one_ rewrite, we return. This makes analysis of the algorithm easier
                    // Sliding window: The function findAndPushAssignmentInBlock looks through a peephole
                    // if nothing has to be done on the peephole, peephole is shifted to the right
                    // Example:
                    //   Assume Stm1;Stm2;Stm3;Stm4;Stm5
                    //     1st Peephole: Stm1
                    //     2nd Peephole: Stm2
                    //     3rd Peephole: Stm3
                    //     4th Peephole: Stm4
                    //     5th Peephole: Stm5
                    //   Every Stm was at least one time peephole
                    let rec traverseBlock (revAlreadyLookedAt:Stm list,peephole:Stm)
                                                         (rightNextToPeephole:Stm list) : (Stm*bool) = 
                        // recursive cases (Stochastic or Choices)
                        let (newStmOfPeephole,changedSomething) = findAndMerge peephole
                        if changedSomething then
                            let newBlock =
                                (revAlreadyLookedAt |> List.rev)
                                @ [newStmOfPeephole]
                                @ rightNextToPeephole
                            (Stm.Block(blockSid,newBlock),true)
                        else if rightNextToPeephole.IsEmpty then
                            //nothing changed at all, so return old statement
                            (stm,false)
                        else
                            // shift peephole to the right
                            let nextRevAlreadyLookedAt = peephole :: revAlreadyLookedAt
                            let nextPeephole = rightNextToPeephole.Head
                            let nextRightNextToPeephole = rightNextToPeephole.Tail
                            traverseBlock (nextRevAlreadyLookedAt,nextPeephole) nextRightNextToPeephole
                    if statements.IsEmpty = false then
                        let firstPeephole = statements.Head
                        let firstRightNextToPeephole = statements.Tail
                        traverseBlock ([],firstPeephole) firstRightNextToPeephole
                    else
                        (stm,false)
                    ///////////// End of rewriting Block
                | Stm.Choice (sid,choices: (Expr option * Stm) list) ->
                    let rec traverseChoices (revAlreadyTraversed:(Expr option * Stm) list) (toTraverse:(Expr option * Stm) list) : (Stm*bool) = 
                        if toTraverse.IsEmpty then
                            (stm,false)
                        else
                            let (choiceToTraverseGuard,choiceToTraverseStm) = toTraverse.Head                                                       
                            match choiceToTraverseStm with
                                | Stm.Block(_,Stm.Choice(_,innerChoices)::[])
                                | Stm.Choice(_,innerChoices) ->
                                    // The main part of this algorithm                                    
                                    let mergeGuards (guard1:Expr option) (guard2:Expr option) : Expr option =
                                        match (guard1,guard2) with
                                            | Some(guard1),Some(guard2) -> Some(Expr.BExpr(guard1,BOp.And,guard2))
                                            | Some(guard1),None -> Some(guard1)
                                            | None,Some(guard2) -> Some(guard2)
                                            | None,None -> None       
                                    let newInnerChoices =
                                        innerChoices |> List.map (fun (innerChoiceGuard,innerChoiceStm) -> (mergeGuards choiceToTraverseGuard innerChoiceGuard,innerChoiceStm) )
                                    let newChoices =
                                        (revAlreadyTraversed |> List.rev)
                                        @ newInnerChoices
                                        @ toTraverse.Tail
                                    let choiceStatement = Stm.Choice (sid,newChoices)
                                    (choiceStatement,true)
                                | _ ->
                                    // recursive case (try to change something inside)
                                    // stochastic statement may propagate upwards
                                    let (traversedChoiceStm,somethingChanged) = findAndMerge choiceToTraverseStm
                                    let traversedChoice = (choiceToTraverseGuard,traversedChoiceStm)
                                    if somethingChanged then
                                        let newChoices =
                                            (revAlreadyTraversed |> List.rev)
                                            @ [(traversedChoice)]
                                            @ toTraverse.Tail
                                        let choiceStatement = Stm.Choice (sid,newChoices)
                                        (choiceStatement,true)
                                    else
                                        //nothing was changed by toTraverse.Head, so try the next candidate in the list
                                        traverseChoices (toTraverse.Head::revAlreadyTraversed) (toTraverse.Tail)
                    traverseChoices [] choices
                | _ ->
                    (stm,false)
        
        let rec findAndMergeUntilFixpoint (stm:Stm) =
            let (newStm,wasChanged) = findAndMerge stm
            if wasChanged then
                findAndMergeUntilFixpoint newStm
            else
                stm
        let! model = getTsamModel ()
        let allChoicesMergedAtTheBeginningBody = findAndMergeUntilFixpoint (model.Body)
        let allChoicesMergedAtTheBeginningModel = 
            { model with
                Pgm.Body = allChoicesMergedAtTheBeginningBody
            }
        do! updateTsamModel allChoicesMergedAtTheBeginningModel
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
        
        let! state = getState ()
        let uniqueStatementIdGenerator = state.Pgm.UniqueStatementIdGenerator
        let rec findAndMerge (stm:Stm) : (Stm*bool) = //returns Stm (without pulled) * Stm to pull (if Stm to pull exists) * changedSomething
            match stm with
                | Stm.Block (blockSid,statements:Stm list) ->
                    ///////////// Here we rewrite the block. Result must be block                    
                    // After _one_ rewrite, we return. This makes analysis of the algorithm easier
                    // Sliding window: The function findAndPushAssignmentInBlock looks through a peephole
                    // if nothing has to be done on the peephole, peephole is shifted to the right
                    // Example:
                    //   Assume Stm1;Stm2;Stm3;Stm4;Stm5
                    //     1st Peephole: Stm1
                    //     2nd Peephole: Stm2
                    //     3rd Peephole: Stm3
                    //     4th Peephole: Stm4
                    //     5th Peephole: Stm5
                    //   Every Stm was at least one time peephole
                    let rec traverseBlock (revAlreadyLookedAt:Stm list,peephole:Stm)
                                                         (rightNextToPeephole:Stm list) : (Stm*bool) = 
                        // recursive cases (Stochastic or Choices)
                        let (newStmOfPeephole,changedSomething) = findAndMerge peephole
                        if changedSomething then
                            let newBlock =
                                (revAlreadyLookedAt |> List.rev)
                                @ [newStmOfPeephole]
                                @ rightNextToPeephole
                            (Stm.Block(blockSid,newBlock),true)
                        else if rightNextToPeephole.IsEmpty then
                            //nothing changed at all, so return old statement
                            (stm,false)
                        else
                            // shift peephole to the right
                            let nextRevAlreadyLookedAt = peephole :: revAlreadyLookedAt
                            let nextPeephole = rightNextToPeephole.Head
                            let nextRightNextToPeephole = rightNextToPeephole.Tail
                            traverseBlock (nextRevAlreadyLookedAt,nextPeephole) nextRightNextToPeephole
                    if statements.IsEmpty = false then
                        let firstPeephole = statements.Head
                        let firstRightNextToPeephole = statements.Tail
                        traverseBlock ([],firstPeephole) firstRightNextToPeephole
                    else
                        (stm,false)
                    ///////////// End of rewriting Block
                | Stm.Choice (sid,choices: (Expr option * Stm) list) ->
                    let rec traverseChoices (revAlreadyTraversed:(Expr option * Stm) list) (toTraverse:(Expr option * Stm) list) : (Stm*bool) = 
                        if toTraverse.IsEmpty then
                            (stm,false)
                        else
                            let (choiceToTraverseGuard,choiceToTraverseStm) = toTraverse.Head
                            // recursive case (try to change something inside)
                            // stochastic statement may propagate upwards
                            let (traversedChoiceStm,somethingChanged) = findAndMerge choiceToTraverseStm
                            let traversedChoice = (choiceToTraverseGuard,traversedChoiceStm)
                            if somethingChanged then
                                let newChoices =
                                    (revAlreadyTraversed |> List.rev)
                                    @ [(traversedChoice)]
                                    @ toTraverse.Tail
                                let choiceStatement = Stm.Choice (sid,newChoices)
                                (choiceStatement,true)
                            else
                                //nothing was changed by toTraverse.Head, so try the next candidate in the list
                                traverseChoices (toTraverse.Head::revAlreadyTraversed) (toTraverse.Tail)
                    traverseChoices [] choices

                | Stm.Stochastic (stochasticSid,stochasticChoices: (Expr*Stm) list) ->
                    let rec traverseStochasticChoices (revAlreadyTraversed:(Expr*Stm) list) (toTraverse:(Expr*Stm) list) : (Stm*bool) = 
                        if toTraverse.IsEmpty then
                            (stm,false)
                        else
                            let (stochasticChoiceToTraverseExpr,stochasticChoiceToTraverseStm) = toTraverse.Head
                            match stochasticChoiceToTraverseStm with
                                | Stm.Block(_,Stm.Stochastic(_,innerStochasticChoices)::[])
                                | Stm.Stochastic(_,innerStochasticChoices) ->
                                    // The main part of this algorithm
                                    let combineInnerChoiceWithOuterChoice (innerStochasticChoiceExpr,innerStochasticChoiceStm) =
                                        let combinedExpr = Expr.BExpr(stochasticChoiceToTraverseExpr,BOp.Multiply,innerStochasticChoiceExpr)
                                        (combinedExpr,innerStochasticChoiceStm)
                                    let newInnerStochasticChoices =
                                        innerStochasticChoices |> List.map combineInnerChoiceWithOuterChoice
                                    let newStochasticChoices =
                                        (revAlreadyTraversed |> List.rev)
                                        @ newInnerStochasticChoices
                                        @ toTraverse.Tail
                                    let choiceStatement = Stm.Stochastic (stochasticSid,newStochasticChoices)
                                    (choiceStatement,true)
                                // InnerStochastic
                                // here the magic happens
                                | _ ->
                                    // recursive case (try to change something inside)
                                    // stochastic statement may propagate upwards
                                    let (traversedStochasticChoice,somethingChanged) = findAndMerge stochasticChoiceToTraverseStm
                                    if somethingChanged then
                                        let newChoices =
                                            (revAlreadyTraversed |> List.rev)
                                            @ [(stochasticChoiceToTraverseExpr,traversedStochasticChoice)]
                                            @ toTraverse.Tail
                                        let stochasticStatement = Stm.Stochastic (stochasticSid,newChoices)
                                        (stochasticStatement,true)
                                    else
                                        //nothing was changed by toTraverse.Head, so try the next candidate in the list
                                        traverseStochasticChoices ((stochasticChoiceToTraverseExpr,stochasticChoiceToTraverseStm)::revAlreadyTraversed) (toTraverse.Tail)
                    traverseStochasticChoices [] stochasticChoices
                | _ ->
                    (stm,false)
        
        let rec findAndMergeUntilFixpoint (stm:Stm) =
            let (newStm,wasChanged) = findAndMerge stm
            if wasChanged then
                findAndMergeUntilFixpoint newStm
            else
                stm
        let! model = getTsamModel ()
        let allStochasticsMergedAtTheEndBody = findAndMergeUntilFixpoint (model.Body)
        let allStochasticsMergedAtTheEndModel = 
            { model with
                Pgm.Body = allStochasticsMergedAtTheEndBody
            }
        do! updateTsamModel allStochasticsMergedAtTheEndModel
        return ()        
    }

    let transformTsamToTsamInGuardToAssignmentForm () : TsamWorkflowFunction<_,unit> = workflow {
        let! model = getState()
        if model.Pgm.CodeForm = CodeForm.Passive then
            failwith "passive form cannot be used with this algorithm"
            // Assume Single Assignment Form. TODO: Default form may also work. Examine. Passive form does not work.
        else
            do! phase1TreeifyAndNormalize ()
            do! phase2PushAssignmentsNotAtTheEnd ()
            do! phase3PullChoicesTowardsBeginning ()
            do! phase4PullAssertionsAndAssumptionsTowardsBeginning ()
            do! phase5MergeChoicesAtTheBeginning ()
            do! phase6MergeStochasticsAtTheEnd ()
            return ()
    }

        


    // GuardWithAssignmentModel is actually somehow a Spg with only one state. Thus, the state
    // can easily be abstracted away.

    type FinalVariableAssignments = {
        Assignments : Map<Var,Expr>;
    }
    type StochasticAssignment = {
        Probability : Expr;
        Assignments : FinalVariableAssignments;
    }

    [<RequireQualifiedAccessAttribute>]
    type Assignments =
        | Deterministic of Guard:Expr * Assignments:FinalVariableAssignments
        | Stochastic of Guard:Expr * Assignments:(StochasticAssignment list)
            
    type GuardWithAssignmentModel = {
        Globals : VarDecl list;
        Assignments : Assignments list;
    }

    
    let guardWithAssignmentModelToString (gwam:GuardWithAssignmentModel) : string =
        let exportExpr (expr:Expr) =
            let exported = TsamToString.exportExpr expr SamToStringHelpers.AstToStringState.initial
            exported.ToString()
        let exportVarDecl (varDecl:VarDecl) =
            let exported = TsamToString.exportGlobalVarDecl varDecl SamToStringHelpers.AstToStringState.initial
            exported.ToString()
        let globals = gwam.Globals |> List.map exportVarDecl |> String.concat ""
        let assigns =
            let finalAssignments (assignments:FinalVariableAssignments) : string =
                let varAssignToString (var,expr) =
                    let varName = match var with | Var.Var(name) -> name
                    sprintf "      %s := %s;\n" (varName) (exportExpr expr)
                assignments.Assignments |> Map.toList |> List.map varAssignToString |> String.concat ""
            let deterministicAssign (guard:Expr,assignment:FinalVariableAssignments) : string =                
                sprintf "Case %s:\n%s" (exportExpr guard) (finalAssignments assignment)
            let stochasticAssign (guard:Expr,assignment:StochasticAssignment list) : string =
                let stochasticCase (stochasticAssignment:StochasticAssignment) =
                    sprintf "   Probability: %s\n%s" (exportExpr stochasticAssignment.Probability) (finalAssignments stochasticAssignment.Assignments)
                let cases = assignment |> List.map stochasticCase |> String.concat ""
                sprintf "Case %s:\n%s" (exportExpr guard) (cases)
            let assign (assign:Assignments) =
                match assign with
                    | Assignments.Deterministic (guard,assignment) -> deterministicAssign (guard,assignment)
                    | Assignments.Stochastic(guard,stoAssignment) -> stochasticAssign (guard,stoAssignment)
            gwam.Assignments |> List.map assign |> String.concat ""
        let output = sprintf "Global State Variables:\n%sAssignments:\n%s" globals assigns
        output


    
    let transformGwaTsamToGwaModel (pgm:Tsam.Pgm) : GuardWithAssignmentModel =
        // The algorithm also ensures variables never written to keep their value
        let skipStm = Stm.Block(pgm.UniqueStatementIdGenerator (),[])
        
        let initialValuation =
            // add for each globalVar a self assignment
            let globalInit = pgm.Globals |> List.fold (fun (acc:Map<Var,Expr>) var -> acc.Add(var.Var,Expr.Read(var.Var))) Map.empty<Var,Expr>
            // every local variable should have its default value
            let globalAndLocalInit = pgm.Locals |> List.fold (fun (acc:Map<Var,Expr>) var -> acc.Add(var.Var,Expr.Literal(var.Type.getDefaultValue))) globalInit
            globalAndLocalInit
            
        let finalVars = pgm.NextGlobal |> Map.toList |> List.map (fun (original,final) -> final) |> Set.ofList  
        let nextGlobalToCurrent = pgm.NextGlobal |> Map.toList |> List.map (fun (oldVar,newVar) -> (newVar,oldVar) ) |> Map.ofList

        let redirectFinalVars (variableValuation:Map<Var,Expr>) : Map<Var,Expr> =
            variableValuation
                |> Map.filter (fun key value -> finalVars.Contains key)
                |> Map.toList
                |> List.map (fun (oldkey,value) -> (nextGlobalToCurrent.Item oldkey,value)) // use the nextGlobal redirection here
                |> Map.ofList

        let processWrites (stm:Stm) : FinalVariableAssignments =
            match stm with
                | Stm.Block(_,statements) ->
                    let rec traverseBlock (currentValuation:Map<Var,Expr>)
                                          (toTraverse:Stm list) : (Map<Var,Expr>) = //returns the assumes and rest of the block (Block with a Stochastic or with a bunch of assignments)
                        if toTraverse.IsEmpty then
                            currentValuation
                        else
                            let peepholeStm = toTraverse.Head
                            match peepholeStm with
                                | Stm.Write (_,var,expr) ->
                                    let newExpr = expr.rewriteExpr_varsToExpr currentValuation
                                    let newValuation = currentValuation.Add(var,newExpr)
                                    traverseBlock (newValuation) (toTraverse.Tail)
                                | _ ->
                                    failwith "BUG: Structure of Tsam.Pgm.Body was not in GwaTsam Form"
                    let assignments = traverseBlock (initialValuation) statements
                    {
                        FinalVariableAssignments.Assignments = (assignments |> redirectFinalVars)
                    }
                | Stm.Write(_,var,expr) ->
                    let newExpr = expr.rewriteExpr_varsToExpr initialValuation
                    let newValuation = initialValuation.Add(var,newExpr)
                    {
                        FinalVariableAssignments.Assignments = (newValuation |> redirectFinalVars)
                    }
                | _ -> failwith "BUG: Structure of Tsam.Pgm.Body was not in GwaTsam Form"
        
        let processStochastic (guard:Expr,stm:Stm) : Assignments =
            match stm with
                | Stm.Block(_,Stm.Stochastic(_,stochasticChoices)::[])
                | Stm.Stochastic(_,stochasticChoices) ->
                    let createStochasticAssignment (probability:Expr,assignments:Stm) =
                        {
                            StochasticAssignment.Probability = probability
                            StochasticAssignment.Assignments = processWrites assignments
                        }
                    let stochasticAssignments = stochasticChoices |> List.map createStochasticAssignment
                    Assignments.Stochastic(guard,stochasticAssignments)
                | _ ->
                    Assignments.Deterministic(guard,processWrites stm)
        
        let processAssumptionsAndAssertions (guardOfChoice:Expr option,stm:Stm) : Assignments =
            match stm with
                | Stm.Block(blockSid,statements) ->                    
                    let rec traverseBlock (revAlreadyToAssume:Expr list)
                                          (toTraverse:Stm list) : (Expr list*Stm) = //returns the assumes and rest of the block (Block with a Stochastic or with a bunch of assignments)
                        if toTraverse.IsEmpty then
                            (revAlreadyToAssume |> List.rev,skipStm)
                        else
                            let peepholeStm = toTraverse.Head
                            match peepholeStm with
                                | Stm.Assume (_,expr) ->
                                    traverseBlock (expr::revAlreadyToAssume) (toTraverse.Tail)
                                | Stm.Assert (_,expr) ->
                                    failwith "Not doing proof obligations, yet" //Assert: TODO: Generate proof obligations. We even could calculate the probability of a violation of an assertion.
                                | _ ->
                                    let alreadyToAssume = revAlreadyToAssume |> List.rev
                                    let restBlock = toTraverse
                                    (alreadyToAssume,Stm.Block(blockSid,restBlock))
                    let (assumes,restBlock) = traverseBlock [] statements
                    let guard = createAndedExpr assumes
                    processStochastic (guard,restBlock)
                | Stm.Assume(_,expr) ->
                    processStochastic (expr,skipStm)
                | Stm.Assert(_,_expr) ->
                    failwith "Not doing proof obligations, yet" //Assert: TODO: Generate proof obligations. We even could calculate the probability of a violation of an assertion.
                | _ ->
                    processStochastic (Expr.Literal(Val.BoolVal(true)),stm)

        let processChoices (stm:Stm) : Assignments list =
            match stm  with
                | Stm.Block(_,Stm.Choice(_,choices)::[])
                | Stm.Choice(_,choices) ->
                    choices |> List.map (processAssumptionsAndAssertions)
                | _ ->
                    [processAssumptionsAndAssertions (None,stm)]
        {
            GuardWithAssignmentModel.Globals = pgm.Globals;
            GuardWithAssignmentModel.Assignments = processChoices pgm.Body;
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
                    
               


    let transformTsamToGwaModelWorkflow<'traceableOfOrigin> () : ExogenousWorkflowFunction<TsamMutable.MutablePgm<'traceableOfOrigin>,GuardWithAssignmentModelTracer<'traceableOfOrigin>> = workflow {
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

    let modelToStringWorkflow<'traceableOfOrigin> () : WorkflowFunction<GuardWithAssignmentModelTracer<'traceableOfOrigin>,string,unit> = workflow {
        let! model = getState ()
        let asString = guardWithAssignmentModelToString model.GuardWithAssignmentModel
        do! updateState asString
    }
    