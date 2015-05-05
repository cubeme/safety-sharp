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
open SafetySharp.Models.Sam

module internal TsamChangeIdentifier =

    open Tsam
    open SafetySharp.Models.SamHelpers
    
    type NameGenerator = Set<string> -> string -> string

    type ChangeIdentifierState = {
        TakenNames : Set<string>;
        OldToNew : Map<Var,Var>;
        NameGenerator : NameGenerator;
    }
        with
            static member initial (forbiddenNames:Set<string>) (nameGenerator:NameGenerator) =
                {
                    ChangeIdentifierState.TakenNames = forbiddenNames;
                    OldToNew = Map.empty<Var,Var>;
                    NameGenerator = nameGenerator;
                }
            member this.generateNewName (based_on:string) : string =
                this.NameGenerator this.TakenNames based_on

            member this.generateNewVar (oldVar:Var) : (Var*ChangeIdentifierState) =
                let newVarName = this.generateNewName oldVar.getName
                let newVar = Var(newVarName)
                let newState=
                    { this with
                        ChangeIdentifierState.TakenNames = this.TakenNames.Add newVarName;
                        ChangeIdentifierState.OldToNew = this.OldToNew.Add (oldVar,newVar)
                    }
                (newVar,newState)

        
    let rec transformExpr (state:ChangeIdentifierState) (expr:Expr) : Expr =
        match expr with
            | Literal (_)->
                expr
            | UExpr (operand,operator) ->
                Expr.UExpr(transformExpr state operand,operator)
            | BExpr (leftExpression,operator,rightExpression ) ->
                Expr.BExpr(transformExpr state leftExpression,operator,transformExpr state rightExpression)
            | Read (variable) ->
                Expr.Read(state.OldToNew.Item variable)
            | ReadOld (variable) ->
                Expr.ReadOld(state.OldToNew.Item variable)

    let rec transformStm (state:ChangeIdentifierState) (stm:Stm) : Stm =
        match stm with
            | Stm.Assert (sid,expr) ->
                Stm.Assert(sid,transformExpr state expr)
            | Stm.Assume (sid,expr) ->
                Stm.Assume(sid,transformExpr state expr)
            | Stm.Block (sid,statements) ->
                Stm.Block(sid,statements |> List.map (transformStm state) )
            | Stm.Choice (sid,clauses) ->
                Stm.Choice(sid,clauses |> List.map (transformStm state))
            | Stm.Stochastic (sid,clauses) ->
                Stm.Stochastic(sid,clauses |> List.map (fun (prob,stm) -> (transformExpr state prob,transformStm state stm)))
            | Write (sid,variable:Var, expression:Expr) ->
                Stm.Write(sid,state.OldToNew.Item variable,transformExpr state expression)
    
    let changeNamesPgm (state:ChangeIdentifierState) (samPgm:Pgm) : Pgm =
        let currentVars = seq {
            yield! samPgm.Globals |> List.map (fun var -> var.Var)
            yield! samPgm.Locals |> List.map (fun var -> var.Var)
        }
        let stateWithAllNames =
            { state with
                ChangeIdentifierState.TakenNames = Set.union state.TakenNames (currentVars |> Seq.map (fun var->var.getName) |> Set.ofSeq);
            }
        let newState =
            let generateAndAddToList (state:ChangeIdentifierState) (varToTransform:Var): (ChangeIdentifierState) =
                let (_,newState) = state.generateNewVar varToTransform
                newState
            Seq.fold generateAndAddToList (stateWithAllNames) currentVars
        
        let newGlobals =
            let transformGlobal (globalVar:GlobalVarDecl) =
                { globalVar with
                    GlobalVarDecl.Var = newState.OldToNew.Item globalVar.Var
                }
            samPgm.Globals |> List.map transformGlobal

        let newLocals =
            let transformLocal (localVar:LocalVarDecl) =
                { localVar with
                    LocalVarDecl.Var = newState.OldToNew.Item localVar.Var
                }
            samPgm.Locals |> List.map transformLocal        
        let newNextGlobal =
            samPgm.NextGlobal |> Map.toList
                              |> List.map (fun (fromOldVar,toOldVar) -> (newState.OldToNew.Item fromOldVar,newState.OldToNew.Item toOldVar) )
                              |> Map.ofList
        { samPgm with
            Pgm.Globals = newGlobals;
            Pgm.Locals = newLocals;
            Pgm.Body = transformStm newState samPgm.Body;
            Pgm.NextGlobal = newNextGlobal;
        }

    
    
    open SafetySharp.Workflow
    
    let changeIdentifiers (forbiddenNames:Set<string>) : WorkflowFunction<Tsam.Pgm,Tsam.Pgm,unit> = workflow {
        let! pgm = getState ()
        
        let changeIdsState = ChangeIdentifierState.initial forbiddenNames SafetySharp.FreshNameGenerator.namegenerator_c_like
        let newPgm = changeNamesPgm changeIdsState pgm
        
        do! updateState newPgm
    }


