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

module internal SamChangeIdentifier =

    open SafetySharp.Models.Sam
    open SafetySharp.Models.SamHelpers
    
    type NameGenerator = Set<string> -> string -> string

    type ChangeIdentifierState = {
        TakenNames : Set<string>;
        OldToNew : Map<Element,Element>;
        NameGenerator : NameGenerator;
    }
        with
            static member initial (forbiddenNames:Set<string>) (nameGenerator:NameGenerator) =
                {
                    ChangeIdentifierState.TakenNames = forbiddenNames;
                    OldToNew = Map.empty<Element,Element>;
                    NameGenerator = nameGenerator;
                }
            member this.generateNewName (based_on:string) : string =
                this.NameGenerator this.TakenNames based_on

            member this.generateNewElement (oldVar:Element) : (Element*ChangeIdentifierState) =
                let newVarName = this.generateNewName oldVar.getName
                let newVar =
                    match oldVar with
                        | Element.GlobalVar _ -> Element.GlobalVar (Var(newVarName))
                        | Element.LocalVar _ -> Element.LocalVar (Var(newVarName))                    
                let newState=
                    { this with
                        ChangeIdentifierState.TakenNames = this.TakenNames.Add newVarName;
                        ChangeIdentifierState.OldToNew = this.OldToNew.Add (oldVar,newVar)
                    }
                (newVar,newState)

    
    (*
    let namegenerator_c_like_random (takenNames:Set<string>) (based_on:string) : string =
        // * https://msdn.microsoft.com/en-us/library/e7f8y25b.aspx
        // * Rule-Type: [a-zA-Z_][a-zA-Z0-9_]* without forbidden names (keywords)
        // * note: omit 2 underscores
        // * max length of identifier 31 (ansi) or 247 (microsoft). let's stay with 31
        // try to find a real short name (around 20 characters)

        based_on

    let namegenerator_c_like_basedon (takenNames:Set<string>) (based_on:string) : string =
        // * https://msdn.microsoft.com/en-us/library/e7f8y25b.aspx
        // * Rule-Type: [a-zA-Z_][a-zA-Z0-9_]* without forbidden names (keywords)
        // * note: omit 2 underscores
        // * max length of identifier 31 (ansi) or 247 (microsoft). let's stay with 31
        
        based_on
    *)
    
    let rec transformExpr (oldToNew : Map<Element,Element>) (expr:Expr) : Expr =
        match expr with
            | Literal (_)->
                expr
            | UExpr (operand,operator) ->
                Expr.UExpr(transformExpr oldToNew operand,operator)
            | BExpr (leftExpression,operator,rightExpression ) ->
                Expr.BExpr(transformExpr oldToNew leftExpression,operator,transformExpr oldToNew rightExpression)
            | Read (variable) ->
                Expr.Read(oldToNew.Item variable)
            | ReadOld (variable) ->
                Expr.ReadOld(oldToNew.Item variable)
            | Expr.IfThenElseExpr (guardExpr, thenExpr, elseExpr) ->
                Expr.IfThenElseExpr(transformExpr oldToNew guardExpr,transformExpr oldToNew thenExpr,transformExpr oldToNew elseExpr)

    let rec transformStm (oldToNew : Map<Element,Element>) (stm:Stm) : Stm =
        match stm with
            | Block (statements) ->
                Stm.Block(statements |> List.map (transformStm oldToNew) )
            | Choice (clauses : Clause list) ->
                let transformClause (clause:Clause) : Clause =
                    {
                        Clause.Guard = transformExpr oldToNew clause.Guard;
                        Clause.Statement = transformStm oldToNew clause.Statement
                    }
                Stm.Choice(clauses |> List.map transformClause)
            | Stochastic (stochasticChoice: (Expr*Stm) list) ->
                let transformStochasticChoice (prob,stm) : Expr*Stm=
                    (transformExpr oldToNew prob, transformStm oldToNew stm)
                Stm.Stochastic(stochasticChoice |> List.map transformStochasticChoice)
            | Write (element:Element, expression:Expr) ->
                Stm.Write(oldToNew.Item element,transformExpr oldToNew expression)
    
    let changeNamesPgm (state:ChangeIdentifierState) (samPgm:Pgm) : (Pgm*Map<Element,Element>) = // returns new program * forward tracing map
        let currentElements = seq {
            yield! samPgm.Globals |> List.map (fun var -> Element.GlobalVar var.Var)
            yield! samPgm.Locals |> List.map (fun var -> Element.LocalVar var.Var)
        }
        let stateWithAllNames =
            { state with
                ChangeIdentifierState.TakenNames = Set.union state.TakenNames (currentElements |> Seq.map (fun var->var.getName) |> Set.ofSeq);
            }
        let newState =
            let generateAndAddToList (state:ChangeIdentifierState) (varToTransform:Element): (ChangeIdentifierState) =
                let (_,newState) = state.generateNewElement varToTransform
                newState
            Seq.fold generateAndAddToList (stateWithAllNames) currentElements
        
        let newGlobals =
            let transformGlobal (globalVar:GlobalVarDecl) =
                { globalVar with
                    GlobalVarDecl.Var =
                        match newState.OldToNew.Item (Element.GlobalVar globalVar.Var) with
                            | Element.GlobalVar var -> var
                            | _ -> failwith "OldToNew should map a globalVar to a globalVar"
                }
            samPgm.Globals |> List.map transformGlobal

        let newLocals =
            let transformLocal (localVar:LocalVarDecl) =
                { localVar with
                    LocalVarDecl.Var =
                        match newState.OldToNew.Item (Element.LocalVar localVar.Var) with
                            | Element.LocalVar var -> var
                            | _ -> failwith "OldToNew should map a localVar to a localVar"
                }
            samPgm.Locals |> List.map transformLocal

        let samPgm =
            {
                Pgm.Globals = newGlobals;
                Pgm.Locals = newLocals;
                Pgm.Body = transformStm newState.OldToNew samPgm.Body;
            }
        (samPgm,newState.OldToNew)

    



