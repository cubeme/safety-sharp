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
            | Stm.Assert (sid,expr) ->
                Stm.Assert(sid,transformExpr oldToNew expr)
            | Stm.Assume (sid,expr) ->
                Stm.Assume(sid,transformExpr oldToNew expr)
            | Stm.Block (sid,statements) ->
                Stm.Block(sid,statements |> List.map (transformStm oldToNew) )
            | Stm.Choice (sid,clauses) ->
                Stm.Choice(sid,clauses |> List.map (fun (guard,stm) ->
                                                        let newGuard = if guard.IsSome then Some(transformExpr oldToNew guard.Value) else None;
                                                        (newGuard,transformStm oldToNew stm))
                                                   )
            | Stm.Stochastic (sid,clauses) ->
                Stm.Stochastic(sid,clauses |> List.map (fun (prob,stm) -> (transformExpr oldToNew prob,transformStm oldToNew stm)))
            | Write (sid,element:Element, expression:Expr) ->
                Stm.Write(sid,oldToNew.Item element,transformExpr oldToNew expression)
    
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

  
        let newNextGlobal =
            samPgm.NextGlobal |> Map.toList
                              |> List.map (fun (fromOldVar,toOldVar) -> (newState.OldToNew.Item fromOldVar,newState.OldToNew.Item toOldVar) )
                              |> Map.ofList
        let samPgm =
            { samPgm with
                Pgm.Globals = newGlobals;
                Pgm.Locals = newLocals;
                Pgm.ElementToType = TsamHelpers.createElementToType (newGlobals,newLocals);
                Pgm.Body = transformStm newState.OldToNew samPgm.Body;
                Pgm.NextGlobal = newNextGlobal;
            }
        (samPgm,newState.OldToNew)

    
    
    open SafetySharp.Workflow
    
    let changeIdentifiers<'traceableOfOrigin> (forbiddenNames:Set<string>) : EndogenousWorkflowFunction<TsamTracer.TsamTracer<'traceableOfOrigin>> = workflow {
        let! mutablePgm = getState ()
        
        let changeIdsState = ChangeIdentifierState.initial forbiddenNames SafetySharp.FreshNameGenerator.namegenerator_c_like
        
        let (newPgm,forwardTrace) = changeNamesPgm changeIdsState (mutablePgm.Pgm)
        //let forwardTrace = forwardTrace |> Map.toList |> List.map (fun (samVar,promelaVar) -> (Sam.Traceable(samVar),promelaVar.getName) ) |> Map.ofList
        
        let tracer (oldValue:'traceableOfOrigin) =
            let beforeTransform = mutablePgm.ForwardTracer oldValue
            match beforeTransform with
                | Traceable(_var) ->
                    match forwardTrace.Item (Element.GlobalVar _var) with
                        | Element.GlobalVar (_var) -> Traceable.Traceable(_var)
                        | _ -> failwith "Not expected"
                | TraceableRemoved(reason) ->
                    Traceable.TraceableRemoved(reason)


        let newTsamTracer =
            { mutablePgm with
                TsamTracer.TsamTracer.Pgm=newPgm;
                TsamTracer.TsamTracer.ForwardTracer=tracer;
            }
        do! updateState newTsamTracer
    }


