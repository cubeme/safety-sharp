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

namespace SafetySharp.Models

module internal TsamChecks =
    open Tsam

    let rec isTreeForm (stm:Stm) : bool =
        let rec containsNoSplit (stm:Stm) : bool =
            match stm with
                | Stm.Assert _
                | Stm.Assume _
                | Stm.Write _ ->
                    true
                | Stm.Block (_,stmts) ->
                    stmts |> List.forall containsNoSplit
                | Stm.Choice _
                | Stm.Stochastic _ ->
                    false
        match stm with
            | Stm.Assert (sid,expr) ->
                true
            | Stm.Assume (sid,expr) ->
                true
            | Stm.Block (sid,stmts) ->
                if stmts.IsEmpty then
                    true
                else
                    let elementsBeforeLastElement,lastElement =
                        let rec divideInTwoGroups (elementsBeforeLastElementRev:Stm list) (elementsToTraverse:Stm list) : (Stm list)*Stm =
                            if elementsToTraverse.Tail.IsEmpty then
                                (elementsBeforeLastElementRev |> List.rev,elementsToTraverse.Head)
                            else
                                divideInTwoGroups (elementsToTraverse.Head :: elementsBeforeLastElementRev) elementsToTraverse.Tail
                        divideInTwoGroups [] stmts
                    let elementsBeforeLastElementContainNoSplit =
                        elementsBeforeLastElement |> List.forall containsNoSplit
                    if not(elementsBeforeLastElementContainNoSplit) then
                        false // no tree form
                    else
                        isTreeForm lastElement //depends on the last Element
            | Stm.Choice (sid,choices:(Expr option * Stm) list) ->
                choices |> List.forall (fun (_,choiceStm)-> isTreeForm choiceStm)
            | Stm.Stochastic (sid,stochasticChoices) ->
                stochasticChoices |> List.forall (fun (_,choiceStm)-> isTreeForm choiceStm)
            | Stm.Write (sid,var,expr) ->
                true
            
    let rec hasBlocksNestedInBlocks (stm:Stm) : bool =
        let rec containsABlockDirectly (stm:Stm) : bool =
            match stm with
                | Stm.Assert _
                | Stm.Assume _
                | Stm.Write _
                | Stm.Choice _
                | Stm.Stochastic _ ->
                    false
                | Stm.Block _ ->
                    true
        match stm with
            | Stm.Assert (sid,expr) ->
                false
            | Stm.Assume (sid,expr) ->
                false
            | Stm.Block (sid,stmts) ->
                stmts |> List.exists containsABlockDirectly
            | Stm.Choice (sid,choices:(Expr option * Stm) list) ->
                choices |> List.exists (fun (_,choiceStm)-> hasBlocksNestedInBlocks choiceStm)
            | Stm.Stochastic (sid,stochasticChoices) ->
                stochasticChoices |> List.exists (fun (_,choiceStm)-> hasBlocksNestedInBlocks choiceStm)
            | Stm.Write (sid,var,expr) ->
                false