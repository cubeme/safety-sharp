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
    type Pgm with
        member this.getTraceables : Traceable list  =
            this.Globals |> List.map (fun gl -> Sam.Traceable(gl.Var))

    // Extension methods
    type Stm with
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

        member stm.normalizeBlocks (uniqueStatementIdGenerator : unit -> StatementId) =
            // transform stm to be in a form, where no block contains a block directly   
            let isBlock (stm:Stm) : bool =
                match stm with
                    | Stm.Block(_) -> true
                    | _ -> false

            let rec normalizeInABlockStm (sid,statements:Stm list) : (Stm*bool) =
                let getSubStatements (stm:Stm) : ((Stm list)*bool)=
                    match stm with
                        | Stm.Block(sid,statements:Stm list) ->
                            (statements,true)
                        | _ ->
                            let (normalizedOtherStatement,somethingChanged) = normalizeOutOfABlockStm stm
                            ([normalizedOtherStatement],somethingChanged)
                let (flatStatementss,somethingChanged) =
                    statements |> List.map getSubStatements
                               |> List.unzip
                let flatStatements = flatStatementss |> List.collect id
                let somethingChanged = somethingChanged |> List.exists id
                (Stm.Block(sid,flatStatements),somethingChanged)

            and normalizeOutOfABlockStm (stm:Stm) : (Stm*bool) = //returns true, if change occurred
                match stm with
                        | Stm.Block (sid,statements:Stm list) ->
                            normalizeInABlockStm (sid,statements)
                        | Stm.Choice (sid,choices: Stm list) ->
                            let (newChoices,somethingChanged) =
                                choices |> List.map normalizeOutOfABlockStm
                                        |> List.unzip
                            let somethingChanged = somethingChanged |> List.exists id
                            if somethingChanged then
                                (Stm.Choice(sid,newChoices),true)
                            else
                                (stm,false)
                        | Stm.Stochastic (sid,stochasticChoice: (Expr*Stm) list) ->
                            let (newChoices,somethingChanged) =
                                stochasticChoice |> List.map (fun (choiceProb,choiceStm) ->
                                                                  let (newChoiceStm,somethingChanged) = normalizeOutOfABlockStm choiceStm
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
            let rec normalizeStmUntilFixpoint (stm:Stm) =
                let (newStm,wasChanged) = normalizeOutOfABlockStm stm
                if wasChanged then
                    normalizeStmUntilFixpoint newStm
                else
                    stm
            normalizeStmUntilFixpoint stm

                    