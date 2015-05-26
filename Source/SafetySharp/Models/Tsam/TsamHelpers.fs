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

namespace SafetySharp.Models

module internal TsamHelpers =

    open SafetySharp.Models.Tsam
    
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
    
    let unionManyVarMaps<'b when 'b : comparison> (mapsToUnite:Map<Var,'b> list) =
        let rec unionManyVarMaps (united:Map<Var,'b>) (mapsToUnite:Map<Var,'b> list) =
            if mapsToUnite.IsEmpty then
                united
            else
                let newUnited =
                    mapsToUnite.Head |> Map.toList
                                     |> List.fold (fun (united:Map<Var,'b>) (key:Var,value:'b) -> united.Add(key,value)) united
                unionManyVarMaps newUnited mapsToUnite.Tail
        unionManyVarMaps Map.empty<Var,'b> mapsToUnite

    
    // Extension methods
    type Sam.Expr with    
        member expr.rewriteExpr_varsToExpr (currentValuation:Map<Var,Expr>) : Expr =
            match expr with
                | Expr.Literal (_) -> expr
                | Expr.Read (_var) ->                
                    if currentValuation.ContainsKey _var then
                        currentValuation.Item _var
                    else
                        expr
                | Expr.ReadOld (_var) -> expr //old variables keep their value
                | Expr.UExpr (expr,uop) ->
                    Expr.UExpr (expr.rewriteExpr_varsToExpr currentValuation,uop)
                | Expr.BExpr (left, bop, right) ->
                    Expr.BExpr (left.rewriteExpr_varsToExpr currentValuation, bop, right.rewriteExpr_varsToExpr currentValuation)

        member expr.rewriteExpr_varToExpr (varToUpdate:Var,assignVarTo:Expr) : Expr =
            match expr with
                | Expr.Literal (_) -> expr
                | Expr.Read (_var) ->                
                    if varToUpdate = _var then assignVarTo else expr
                | Expr.ReadOld (_var) -> expr //old variables keep their value
                | Expr.UExpr (expr,uop) ->
                    Expr.UExpr (expr.rewriteExpr_varToExpr (varToUpdate,assignVarTo) ,uop)
                | Expr.BExpr (left, bop, right) ->
                    Expr.BExpr (left.rewriteExpr_varToExpr (varToUpdate,assignVarTo), bop, right.rewriteExpr_varToExpr (varToUpdate,assignVarTo))

    // Extension methods
    type Pgm with
        member this.getTraceables : Traceable list  =
            this.Globals |> List.map (fun gl -> Sam.Traceable(gl.Var))

    // Extension methods
    type Stm with
        member stm.prependStatements (uniqueStatementIdGenerator : unit -> StatementId) (stmsToPrepend:Stm list) =
            if stmsToPrepend.IsEmpty then
                stm
            else
                match stm with
                    | Stm.Block (sid,stmnts) ->
                        Stm.Block (sid,stmsToPrepend@stmnts)
                    | _ ->
                        let freshStmId = uniqueStatementIdGenerator ()
                        Stm.Block (freshStmId,stmsToPrepend@[stm])

        member stm.appendStatements (uniqueStatementIdGenerator : unit -> StatementId) (stmsToAppend:Stm list) =
            if stmsToAppend.IsEmpty then
                stm
            else
                match stm with
                    | Stm.Block (sid,stmnts) ->
                        Stm.Block (sid,stmnts@stmsToAppend)
                    | _ ->
                        let freshStmId = uniqueStatementIdGenerator ()
                        Stm.Block (freshStmId,stm::stmsToAppend)

        member stm.unnestBlocks (uniqueStatementIdGenerator : unit -> StatementId) =
            // transform stm to be in a form, where no block contains a block directly 
            let rec unnestOutOfABlockStm (stm:Stm) : (Stm*bool) = //returns true, if change occurred
                match stm with
                        | Stm.Block (sid,statements:Stm list) ->
                            // unnestInABlockStm
                            let getSubStatements (stm:Stm) : ((Stm list)*bool)=
                                match stm with
                                    | Stm.Block(sid,statements:Stm list) ->
                                        (statements,true)
                                    | _ ->
                                        let (normalizedOtherStatement,somethingChanged) = unnestOutOfABlockStm stm
                                        ([normalizedOtherStatement],somethingChanged)
                            let (flatStatementss,somethingChanged) =
                                statements |> List.map getSubStatements
                                           |> List.unzip
                            let flatStatements = flatStatementss |> List.collect id
                            let somethingChanged = somethingChanged |> List.exists id
                            (Stm.Block(sid,flatStatements),somethingChanged)
                        | Stm.Choice (sid,choices: Stm list) ->
                            let (newChoices,somethingChanged) =
                                choices |> List.map unnestOutOfABlockStm
                                        |> List.unzip
                            let somethingChanged = somethingChanged |> List.exists id
                            if somethingChanged then
                                (Stm.Choice(sid,newChoices),true)
                            else
                                (stm,false)
                        | Stm.Stochastic (sid,stochasticChoices: (Expr*Stm) list) ->
                            let (newChoices,somethingChanged) =
                                stochasticChoices |> List.map (fun (choiceProb,choiceStm) ->
                                                                   let (newChoiceStm,somethingChanged) = unnestOutOfABlockStm choiceStm
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
            let rec unnestStmUntilFixpoint (stm:Stm) =
                let (newStm,wasChanged) = unnestOutOfABlockStm stm
                if wasChanged then
                    unnestStmUntilFixpoint newStm
                else
                    stm
            unnestStmUntilFixpoint stm

        member stm.recursiveRenumberStatements (uniqueStatementIdGenerator : unit -> StatementId) =
            let freshId = uniqueStatementIdGenerator ()
            match stm with
                | Tsam.Stm.Assert (_,expr) ->
                    Tsam.Stm.Assert (freshId,expr)
                | Tsam.Stm.Assume (_,expr) ->
                    Tsam.Stm.Assume (freshId,expr)
                | Tsam.Stm.Block (_,statements) ->
                    let newStmnts = statements |> List.map (fun stm -> stm.recursiveRenumberStatements uniqueStatementIdGenerator)
                    Tsam.Stm.Block (freshId,newStmnts)                    
                | Tsam.Stm.Choice (_,choices) ->
                    let newChoices = choices |> List.map (fun stm -> stm.recursiveRenumberStatements uniqueStatementIdGenerator)
                    Tsam.Stm.Choice (freshId,newChoices)                    
                | Tsam.Stm.Stochastic (_,stochasticChoices) ->
                    let newStochasticChoices= stochasticChoices |> List.map (fun (prob,stm) -> (prob,stm.recursiveRenumberStatements uniqueStatementIdGenerator))
                    Tsam.Stm.Stochastic(freshId,newStochasticChoices)
                | Tsam.Stm.Write (_,_var,expr) ->
                    Tsam.Stm.Write(freshId,_var,expr)
            
        member stm.treeifyStm (uniqueStatementIdGenerator : unit -> StatementId) =
            // Example:
            //              ┌─ 4 ─┐                      ┌─ 4 ─ 6
            //    1 ─ 2 ─ 3 ┤     ├ 6    ===>  1 ─ 2 ─ 3 ┤   
            //              └─ 5 ─┘                      └─ 5 ─ 6
            let rec treeifyStm (stm:Stm) : (Stm*bool) = //returns true, if change occurred
                match stm with
                    | Stm.Block (blockSid,statements:Stm list) ->
                        ///////////// Here we rewrite the block. Result must be block
                        let rec treeifyBlockStatements (revAlreadyTreeified:Stm list,alreadySomethingChanged:bool) (toTreeify:Stm list) : (Stm*bool) = 
                            if toTreeify.IsEmpty && not (alreadySomethingChanged) then
                                //nothing changed at all, so return old statement
                                (stm,false)
                            else if toTreeify.IsEmpty && alreadySomethingChanged then
                                let alreadyTreeified = revAlreadyTreeified |> List.rev
                                (Stm.Block (blockSid,alreadyTreeified),true)
                            else
                                let statementToTreeify = toTreeify.Head
                                match statementToTreeify with
                                    | Stm.Choice (sid,choices) ->
                                        let (treeifiedChoices,somethingChanged) = choices |> List.map treeifyStm |> List.unzip
                                        let somethingChanged = somethingChanged |> List.exists id
                                        if toTreeify.Tail.IsEmpty then
                                            // Last statement, everything ok. Nothing to do. We can stop
                                            let newAlreadySomethingChanged = alreadySomethingChanged || somethingChanged
                                            if not (newAlreadySomethingChanged) then
                                                (stm,false)
                                            else
                                                let newChoiceStm = Stm.Choice (sid,treeifiedChoices)
                                                let newTreeified = ((newChoiceStm::revAlreadyTreeified) |> List.rev)
                                                (Stm.Block (blockSid,newTreeified),true)
                                        else
                                            // there are statements after the choice. We need to append them in the choice
                                            let statementsAfterChoice = toTreeify.Tail
                                            let appendStatementsAfterChoiceToChoice (choice:Stm) =
                                                // this is the heart of the algorithm
                                                let newChoice = choice.appendStatements uniqueStatementIdGenerator statementsAfterChoice
                                                let newChoice = newChoice.recursiveRenumberStatements uniqueStatementIdGenerator
                                                newChoice
                                            let newChoiceStm = Stm.Choice(sid,treeifiedChoices |> List.map appendStatementsAfterChoiceToChoice)
                                            // the appended statements do no longer appear after the block. So toTreeify.Tail is no longer necessary.
                                            let newTreeified = ((newChoiceStm::revAlreadyTreeified) |> List.rev)
                                            (Stm.Block(blockSid,newTreeified),true)
                                    | Stm.Stochastic (sid,stochasticChoices) ->                                    
                                        let (treeifiedChoices,somethingChanged) =
                                            stochasticChoices |> List.map (fun (choiceProb,choiceStm) ->
                                                                               let (newChoiceStm,somethingChanged) = treeifyStm choiceStm
                                                                               ((choiceProb,newChoiceStm),somethingChanged)
                                                                           )
                                                              |> List.unzip
                                        let somethingChanged = somethingChanged |> List.exists id

                                        if toTreeify.Tail.IsEmpty then
                                            // Last statement, everything ok. Nothing to do. We can stop
                                            let newAlreadySomethingChanged = alreadySomethingChanged || somethingChanged
                                            if not (newAlreadySomethingChanged) then
                                                (stm,false)
                                            else
                                                let newStochasticStm = Stm.Stochastic (sid,treeifiedChoices)
                                                let newTreeified = ((newStochasticStm::revAlreadyTreeified) |> List.rev)
                                                (Stm.Block (blockSid,newTreeified),true)
                                        else
                                            // there are statements after the choice. We need to append them in the choice
                                            let statementsAfterChoice = toTreeify.Tail
                                            let appendStatementsAfterStochasticToStochastic (expr:Expr,choice:Stm) =
                                                // this is the heart of the algorithm
                                                let newChoice = choice.appendStatements uniqueStatementIdGenerator statementsAfterChoice
                                                let newChoice = newChoice.recursiveRenumberStatements uniqueStatementIdGenerator
                                                (expr,newChoice)
                                            let newStochasticStm = Stm.Stochastic(sid,treeifiedChoices |> List.map appendStatementsAfterStochasticToStochastic)
                                            // the appended statements do no longer appear after the block. So toTreeify.Tail is no longer necessary.
                                            let newTreeified = ((newStochasticStm::revAlreadyTreeified) |> List.rev)
                                            (Stm.Block(blockSid,newTreeified),true)

                                    | _ ->
                                        let (treeifiedStatement,somethingChanged) = treeifyStm statementToTreeify
                                        let newAlreadySomethingChanged = somethingChanged || alreadySomethingChanged
                                        let newRevAlreadyTreeified = treeifiedStatement :: revAlreadyTreeified
                                        treeifyBlockStatements (newRevAlreadyTreeified,newAlreadySomethingChanged) (toTreeify.Tail)
                        treeifyBlockStatements ([],false) statements
                        ///////////// End of rewriting Block
                    | Stm.Choice (sid,choices: Stm list) ->
                        let (newChoices,somethingChanged) =
                            choices |> List.map treeifyStm
                                    |> List.unzip
                        let somethingChanged = somethingChanged |> List.exists id
                        if somethingChanged then
                            (Stm.Choice(sid,newChoices),true)
                        else
                            (stm,false)
                    | Stm.Stochastic (sid,stochasticChoice: (Expr*Stm) list) ->
                        let (newChoices,somethingChanged) =
                            stochasticChoice |> List.map (fun (choiceProb,choiceStm) ->
                                                                let (newChoiceStm,somethingChanged) = treeifyStm choiceStm
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
            let rec treeifyStmUntilFixpoint (stm:Stm) =
                let (newStm,wasChanged) = treeifyStm stm
                if wasChanged then
                    treeifyStmUntilFixpoint newStm
                else
                    stm                    
            let unnestedStm =
                // Note: stm without nested blocks is necessary. It may otherwise happen, that an outer block hides an assignment which should be added.
                // Our algorithm assumes in this example, that the choice is the last statement (it actually is in the inner block).
                // But still we require the outer assignment to be added.
                // Example:
                //      {
                //         choice {
                //            true => {i := 1;}
                //            true => {i := 2;}
                //         }
                //      }
                //      i := i+3;
                // The unnesting is even necessary, if we have a "Stm_A;Stm_B" instead of a "StmBlock.
                // Example:
                //     Stm := ((StmChoice;Stm1);Stm2)
                //     unnested(Stm) := (StmChoice;(Stm1;Stm2))
                //     Now the rule for "Stm_A;Stm_B" when Stm_A is a choice is simply to append Stm_B after each choice.

                stm.unnestBlocks uniqueStatementIdGenerator
            let treeifiedStm =
                // the main part of the algorithm
                treeifyStmUntilFixpoint unnestedStm
            let treeifiedAndUnnestedStm =
                // just to make sure everything is normalized afterwards
                treeifiedStm.unnestBlocks uniqueStatementIdGenerator
            treeifiedAndUnnestedStm

                    