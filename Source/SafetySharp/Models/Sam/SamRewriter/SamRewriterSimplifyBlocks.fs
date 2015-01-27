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


namespace SafetySharp.Models.Sam.Rewriter

module internal SimplifyBlocks = 
    open SafetySharp.Models.Sam

    // Extension methods
    type Stm with
        member stm.removeEmptyBlocks : Stm =
            // not implemented really efficient
            let rec removeEmptyBlocks (stm:Stm) : Stm =
                match stm with
                    | Stm.Block (statements:Stm list) ->
                        let keepStatement (stm:Stm) = if stm = Stm.Block([]) then false else true
                        statements |> List.filter keepStatement
                                   |> List.map removeEmptyBlocks
                                   |> Stm.Block
                    | Stm.Choice (clauses:Clause list) ->
                        let transformOption (clause : Clause) =
                            {
                                Clause.Guard = clause.Guard;
                                Clause.Statement = removeEmptyBlocks clause.Statement;
                            }
                        if clauses.IsEmpty then
                            failwith "BUG: No Choice. Is that what you really want?"
                        else
                            clauses |> List.map transformOption
                                    |> Stm.Choice
                    | Stm.Write (variable:Var, expression:Expr) ->
                        stm // nothing to do
            let rec iterRemove (stm) =
                let removed = removeEmptyBlocks stm
                if removed = stm then
                    //fixpoint reached
                    stm
                else
                    iterRemove removed
            iterRemove stm

        member stm.simplifyBlocksWithOnlyOneStatement : Stm =
            match stm with
                | Stm.Block (statements:Stm list) ->
                    match statements with
                        | [] ->
                            stm
                        | oneInnerStatement::[] ->
                            oneInnerStatement.simplifyBlocksWithOnlyOneStatement //interesting case 1: Block with only one entry
                        | _ ->
                            statements |> List.map (fun stm -> stm.simplifyBlocksWithOnlyOneStatement)
                                       |> Stm.Block
                | Stm.Choice (clauses:Clause list) ->
                    let transformOption (clause : Clause) =
                        {
                            Clause.Guard = clause.Guard;
                            Clause.Statement = clause.Statement.simplifyBlocksWithOnlyOneStatement;
                        }
                    if clauses.IsEmpty then
                        failwith "BUG: No Choice. Is that what you really want?"
                    else
                        clauses |> List.map transformOption
                                |> Stm.Choice
                | Stm.Write (variable:Var, expression:Expr) ->
                    stm // nothing to do

        member stm.simplifyBlocks: Stm =
            stm.removeEmptyBlocks.simplifyBlocksWithOnlyOneStatement //first removeEmptyBlocks must be done

