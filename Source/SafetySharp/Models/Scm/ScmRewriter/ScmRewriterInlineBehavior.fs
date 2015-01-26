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

namespace SafetySharp.Models.Scm

module internal ScmRewriterInlineBehavior =
    open ScmHelpers
    open ScmRewriterBase
    
    // Currently only works in the root component
                
    type ScmRewriterInlineBehaviorFunction<'returnType> = ScmRewriteFunction<unit,'returnType>
    type ScmRewriterInlineBehaviorState = ScmRewriteState<unit>



    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Inline Behavior
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    let findInlineBehavior : ScmRewriterInlineBehaviorFunction<unit> = scmRewrite {    
        let! state = getState
        let compPath = [state.Model.Comp]

        let rec callingDepth (stm:Stm) (currentLevel:int) (stopAtLevel:int) : int =  //TODO: Move to ScmHelpers.fs. May be useful for later applications.
            let rec maxLevel (stmnts:Stm list) (accMaxLevel:int) : int =
                if (stmnts=[]) then
                    accMaxLevel
                else if accMaxLevel=stopAtLevel then
                    stopAtLevel //early quit: Stop searching at depth stopAtLevel
                else
                    let headLevel = callingDepth stmnts.Head currentLevel stopAtLevel
                    let head_or_acc = max headLevel accMaxLevel
                    maxLevel stmnts.Tail head_or_acc
            match stm with
                | Stm.AssignVar (_) -> currentLevel
                | Stm.AssignField (_) -> currentLevel
                | Stm.AssignFault (_) -> currentLevel
                | Stm.Block (stmnts) ->
                    maxLevel stmnts currentLevel
                | Stm.Choice (choices:(Expr * Stm) list) ->                    
                    let stmnts =
                        choices |> List.map (fun (expr,stm) -> stm)
                    maxLevel stmnts currentLevel          
                | Stm.CallPort (reqPort,_params) ->
                    let binding = state.Model.getBindingOfLocalReqPort reqPort
                    //if binding.Kind= BndKind.Delayed then
                    //    failwith "Delayed Bindings cannot be inlined yet" // doesn't matter for depth
                    let provPortsStmts =
                        binding.Source.ProvPort
                            |> state.Model.getProvPortDecls
                            |> List.map (fun portDecl -> portDecl.Behavior.Body)
                    maxLevel provPortsStmts (currentLevel+1)
                | Stm.StepComp (comp) ->
                    failwith "BUG: In this phase Stm.StepComp should not be in any statement"
                | Stm.StepFault (fault) ->
                    let faultStmts =
                        state.Model.Faults
                            |> List.map (fun fault -> fault.Step.Body)
                    maxLevel faultStmts (currentLevel+1)

        if (state.InlineBehavior.IsSome) then
            return ()
        else
            // try to find a behavior, which only contains port calls, which themselves do not call ports            
            // (level calculated by "callingDepth" is exactly 1)            
            let tryFindInProvPorts () : BehaviorWithLocation option =
                let encapsulateResult (port:ProvPortDecl option) : BehaviorWithLocation option =
                    match port with
                        | None -> None
                        | Some (portDecl) -> Some(BehaviorWithLocation.InProvPort(compPath,portDecl,portDecl.Behavior))
                state.Model.ProvPorts |> List.tryFind (fun port -> (callingDepth port.Behavior.Body 0 2)=1)
                                      |> encapsulateResult

            let tryFindInFaultDecls () : BehaviorWithLocation option =
                let encapsulateResult (port:FaultDecl option) : BehaviorWithLocation option =
                    match port with
                        | None -> None
                        | Some (faultDecl) -> Some(BehaviorWithLocation.InFault(compPath,faultDecl,faultDecl.Step))
                state.Model.Faults|> List.tryFind (fun fault -> (callingDepth fault.Step.Body 0 2)=1)
                                  |> encapsulateResult

            let tryFindInStep () : BehaviorWithLocation option =
                let encapsulateResult (port:StepDecl option) : BehaviorWithLocation option =
                    match port with
                        | None -> None
                        | Some (stepDecl) -> Some(BehaviorWithLocation.InStep(compPath,stepDecl,stepDecl.Behavior))
                state.Model.Steps|> List.tryFind (fun step -> (callingDepth step.Behavior.Body 0 2)=1)
                                 |> encapsulateResult

            let candidateToInline : BehaviorWithLocation option =
                match tryFindInProvPorts () with
                    | Some(x) -> Some(x)
                    | None ->
                        match tryFindInFaultDecls () with
                            | Some(x) -> Some(x)
                            | None -> tryFindInStep ()

            match candidateToInline with
                | None -> return ()
                | Some (inlineBehavior) ->
                    let rewriterInlineBehavior = ScmRewriterInlineBehavior.createEmptyFromBehavior inlineBehavior
                    let modifiedState =
                        { state with
                            ScmRewriteState.InlineBehavior = Some(rewriterInlineBehavior);
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
        }
    
    let findCallToInline : ScmRewriterInlineBehaviorFunction<unit> = scmRewrite {
            let! state = getState
            if (state.InlineBehavior.IsNone) then
                return ()
            else
                let inlineBehavior = state.InlineBehavior.Value
                if inlineBehavior.CallToReplace.IsSome then
                    return ()
                else
                    let rec findCall (stm:Stm) (currentPath:StmPath) : (StmPath option) =
                        match stm with
                            | Stm.AssignVar (_) -> None
                            | Stm.AssignField (_) -> None
                            | Stm.AssignFault (_) -> None
                            | Stm.Block (stmnts) ->
                                stmnts |> List.map2 (fun index stm -> (index,stm)) ([0..(stmnts.Length-1)])
                                       |> List.tryPick( fun (index,stm) -> findCall stm (currentPath@[index]))
                            | Stm.Choice (choices:(Expr * Stm) list) ->
                                choices |> List.map2 (fun index stm -> (index,stm)) ([0..(choices.Length-1)])
                                        |> List.tryPick( fun (index,(guard,stm)) -> findCall stm (currentPath@[index]))
                            | Stm.CallPort (_) ->
                                Some(currentPath)
                            | Stm.StepComp (comp) ->
                                failwith "BUG: In this phase Stm.StepComp should not be in any statement"
                                Some(currentPath)
                            | Stm.StepFault (_) ->
                                failwith "BUG: In this phase Stm.StepFault should not be in any statement";
                    let callToInline = findCall inlineBehavior.InlinedBehavior.Body []
                    match callToInline with
                        | None -> return ()
                        | Some (path:StmPath) ->
                            let newInlineBehavior =
                                { inlineBehavior with
                                    ScmRewriterInlineBehavior.CallToReplace=Some(path);
                                }
                            let modifiedState =
                                { state with
                                    ScmRewriteState.InlineBehavior = Some(newInlineBehavior);
                                    ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                                }
                            return! putState modifiedState
        }

    let inlineCall : ScmRewriterInlineBehaviorFunction<unit> = scmRewrite {
            let! state = getState
            if (state.InlineBehavior.IsNone) then
                return ()
            else
                let inlineBehavior = state.InlineBehavior.Value
                if inlineBehavior.CallToReplace.IsNone then
                    return ()
                else
                    let pathToCallToReplace = inlineBehavior.CallToReplace.Value
                    let body = inlineBehavior.InlinedBehavior.Body
                    let callToReplace = body.getSubStatement pathToCallToReplace 
                    match callToReplace with
                        | Stm.AssignVar (_) -> failwith "BUG: Nothing to be inlined at desired position"; return ()
                        | Stm.AssignField (_) -> failwith "BUG: Nothing to be inlined at desired position"; return ()
                        | Stm.AssignFault (_) -> failwith "BUG: Nothing to be inlined at desired position"; return ()
                        | Stm.Block (_) -> failwith "BUG: Nothing to be inlined at desired position"; return ()
                        | Stm.Choice (_) -> failwith "BUG: Nothing to be inlined at desired position"; return ()
                        | Stm.StepComp (comp) ->
                            failwith "BUG: In this phase Stm.StepComp should not be in any statement"; return ()
                        | Stm.StepFault (fault) ->
                            failwith "BUG: In this phase Stm.StepFault should not be in any statement"; return ()
                        | Stm.CallPort (reqPort,_params) ->
                            let binding = state.Model.getBindingOfLocalReqPort reqPort
                            if binding.Kind= BndKind.Delayed then
                                failwith "TODO: Delayed Bindings cannot be inlined yet"
                                return ()
                            else
                                //TODO: rewrite getProvPortDecls: It only gets the ProvPortDecls in the original model and
                                //      does not include the parts, which are in the already rewritten part of the model.
                                //      Move this part into "State".
                                //      Actually, it makes no difference now, but might become a problem later.
                                let provPortDecls = binding.Source.ProvPort |> state.Model.getProvPortDecls
                                assert (provPortDecls.Length = 1) //exactly one provPortDecl should exist. Assume uniteProvPortDecls was called
                                let provPortDecl = provPortDecls.Head
                                    // Note: assure, no name clashes and inside always fresh names are used
                                //let transformLocal  =
                                //    let! newName = getUnusedVarName (sprintf "%s_%s" provPortDecl.getName var.getName)
                                //provPortDecl.Behavior.Locals |> List.iter (fun varDecl -> (varDecl,transformedVarName varDecl) )

                                
                                // Step 1: replace Local:VarDecl by new Local:VarDecl in Statement

                                let! newLocalVarDecls =                                    
                                    let newNameSuggestionsForNewVars =
                                        provPortDecl.Behavior.Locals |> List.map (fun varDecl -> (sprintf "%s_%s" provPortDecl.getName varDecl.getName))
                                    getUnusedVarNames newNameSuggestionsForNewVars
                                let listOldVarDeclsToNewVars =
                                    List.zip provPortDecl.Behavior.Locals newLocalVarDecls
                                let mapOldVarsToNewVars =
                                    listOldVarDeclsToNewVars |> List.map (fun (oldVarDecl,newVar) -> (oldVarDecl.Var,newVar))
                                                             |> Map.ofList                                                                    
                                let newLocalVarDecls =
                                    let createNewVarDecl (oldVarDecl:VarDecl,newVar:Var) : VarDecl =
                                        { oldVarDecl with
                                            VarDecl.Var = newVar
                                        }
                                    listOldVarDeclsToNewVars |> List.map createNewVarDecl

                                let newStatementStep1 = rewriteStm_onlyVars mapOldVarsToNewVars (provPortDecl.Behavior.Body)
                                
                                // Step 2-4: Replace the local vars in the signature.
                                //   replace Params by their actual Fields or LocalVars or declared in the parameters of the caller
                                //   here we need to take a close look: if an expression was used as parameter, add an assignment to a local variable
                                //   add this local variable to the other local variables.
                                //   Otherwise replace the names in-text. Also replace a varCall to a FieldCall in expressions and assignments
                                let localVarToReqPortParam =
                                    List.zip provPortDecl.Params _params

                                // Step 2: ParamExpr.ExprParam
                                //   Every time a localVar is accessed, which is actually an in-parameter (ExprParam) of the ProvPort,
                                //   the localVar is inlined: The localVar is replaced by the expression declared in the call of the provPort.
                                //   Note: InParam may never be written to!
                                //         The Var of an InParam may never be used as InOutParam of a call. (Try to indirectly relief the rule above)
                                let localVarToReqPortExprParamMap =
                                    localVarToReqPortParam |> List.collect (fun (localVarParamDecl,paramReq) ->
                                                              (
                                                                match paramReq with
                                                                    | Param.ExprParam (expr) -> [(localVarParamDecl.Var.Var,expr)]
                                                                    | _ -> []
                                                              ) )
                                                            |> Map.ofList
                                let newStatementStep2 =
                                    rewriteStm_varsToExpr localVarToReqPortExprParamMap newStatementStep1 

                                // Step 3: ParamExpr.InOutVarParam:
                                //      a) replace in each expression, which may occur where ever ReadVar by remapped ReadVar
                                //      b) replace in each statement, which may occur where ever AssignVar by remapped AssignVar
                                //      c) replace in each param, which may occur where ever InOutVarParam by remapped InOutVarParam
                                let localVarToReqPortInOutVarParamMap =
                                    localVarToReqPortParam |> List.collect (fun (localVarParamDecl,paramReq) ->
                                                              (
                                                                match paramReq with
                                                                    | Param.InOutVarParam (var) -> [(localVarParamDecl.Var.Var,var)]
                                                                    | _ -> []
                                                              ) )
                                                            |> Map.ofList
                                let newStatementStep3 =
                                    rewriteStm_onlyVars localVarToReqPortInOutVarParamMap (newStatementStep2) 


                                // Step 4: ParamExpr.InOutFieldParam:
                                //      a) replace in each expression, which may occur where ever ReadVar by remapped ReadField
                                //      b) replace in each statement, which may occur where ever AssignVar by remapped AssignField
                                //      c) replace in each param, which may occur where ever InOutVarParam by remapped InOutFieldParam
                                let localVarToReqPortInOutFieldMap =
                                    localVarToReqPortParam |> List.collect (fun (localVarParamDecl,paramReq) ->
                                                              (
                                                                match paramReq with
                                                                    | Param.InOutFieldParam (field) -> [(localVarParamDecl.Var.Var,field)]
                                                                    | _ -> []
                                                              ) )
                                                            |> Map.ofList
                                let newStatementStep4 =
                                    rewriteStm_varsToFields localVarToReqPortInOutFieldMap newStatementStep3

                                

                                // Step 5: Write back changes into state
                                let newBody = body.replaceSubStatement pathToCallToReplace newStatementStep4
                                let newBehavior =
                                    {
                                        BehaviorDecl.Body = newBody;
                                        BehaviorDecl.Locals = inlineBehavior.InlinedBehavior.Locals @ newLocalVarDecls;
                                    }
                                let newRewriterInlineBehavior =
                                    { inlineBehavior with
                                        ScmRewriterInlineBehavior.CallToReplace = None;
                                        ScmRewriterInlineBehavior.InlinedBehavior = newBehavior;
                                    }
                                let! state = getState // To get the updated state. TODO: Make updates to state only by accessor-functions. Then remove this.
                                let modifiedState =
                                    { state with
                                        ScmRewriteState.InlineBehavior = Some(newRewriterInlineBehavior);
                                        ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                                    }
                                return! putState modifiedState
        }   

    let inlineBehavior : ScmRewriterInlineBehaviorFunction<unit> = scmRewrite {
            // Assert: only inline statements in the root-component

            do! (iterateToFixpoint (scmRewrite {
                do! findCallToInline
                do! inlineCall
            }))
        }

    let writeBackChangedBehavior : ScmRewriterInlineBehaviorFunction<unit> = scmRewrite {
            // Assert: only inline statements in the root-component 
            let! state = getState
            if (state.InlineBehavior.IsNone) then
                return ()
            else
                let inlineBehavior = state.InlineBehavior.Value
                let newModel =
                    match inlineBehavior.BehaviorToReplace with
                        | BehaviorWithLocation.InProvPort (_,provPortDecl,beh) ->
                            let newProvPort =
                                { provPortDecl with
                                    ProvPortDecl.Behavior = inlineBehavior.InlinedBehavior;
                                }
                            state.Model.replaceProvPort(provPortDecl,newProvPort) 
                        | BehaviorWithLocation.InFault (_,faultDecl,beh) ->
                            let newFault =
                                { faultDecl with
                                    FaultDecl.Step = inlineBehavior.InlinedBehavior;
                                }
                            state.Model.replaceFault(faultDecl,newFault) 
                        | BehaviorWithLocation.InStep (_,stepDecl,beh) ->
                            let newStep =
                                { stepDecl with
                                    StepDecl.Behavior = inlineBehavior.InlinedBehavior;
                                }
                            state.Model.replaceStep (stepDecl,newStep) 
                let modifiedState =
                    { state with
                        ScmRewriteState.Model = newModel;
                        ScmRewriteState.InlineBehavior = None;
                        ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                    }
                return! putState modifiedState
        }


        
    let findAndInlineBehavior : ScmRewriterInlineBehaviorFunction<unit> = scmRewrite {
            // Assert: only inline statements in the root-component
            do! findInlineBehavior            
            do! inlineBehavior
            do! writeBackChangedBehavior
        }

    let inlineBehaviors : ScmRewriterInlineBehaviorFunction<unit> = scmRewrite {
            do! (iterateToFixpoint findAndInlineBehavior)
        }