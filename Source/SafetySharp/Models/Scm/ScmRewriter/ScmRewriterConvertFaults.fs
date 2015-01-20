// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

module internal ScmRewriterConvertFaults =
    open ScmHelpers
    open ScmRewriterBase
    
    
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Converting Faults
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    

    let selectRootComponentForConvertingFaults : ScmRewriteFunction<unit> = scmRewrite {
        let! state = getState
        if (state.ConvertFaults.IsSome) then
            return ()
        else
            let rootComp = state.Model
            let rootPath = [state.Model.Comp]
            let convertFaultsState =
                let behaviorsToRewrite =
                    BehaviorWithLocation.collectAllBehaviorsInPath rootComp rootPath
                {
                    ScmRewriterConvertFaults.ArtificialFaultOldToFieldNew = Map.empty<Fault,Field>;
                    ScmRewriterConvertFaults.ArtificialFaultOldToPortNew = Map.empty<Fault,ProvPort*ReqPort>;
                    ScmRewriterConvertFaults.BehaviorsToRewrite = behaviorsToRewrite;
                }
            let modifiedState =
                { state with
                    ScmRewriteState.ChangingSubComponent = rootComp;
                    ScmRewriteState.PathOfChangingSubcomponent = rootPath;
                    ScmRewriteState.ConvertFaults = Some(convertFaultsState);
                    ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                }
            return! putState modifiedState
    }
    
    let replaceFaultByPortsAndFields : ScmRewriteFunction<unit> = scmRewrite {
        let! state = getState
        if (state.ConvertFaults.IsNone) then
            return ()
        else
            let convertFaultsState = state.ConvertFaults.Value
            let! compDecl = getSubComponentToChange
            if compDecl.Faults = [] then
                return ()
            else
                let faultToConvert = compDecl.Faults.Head

                let! reqPort = getUnusedReqPortName  (sprintf "fault_%s_req" faultToConvert.getName)
                let! provPort = getUnusedProvPortName (sprintf "fault_%s_prov" faultToConvert.getName)
                let! field = getUnusedFieldName (sprintf "fault_%s" faultToConvert.getName)

                let! state = getState // To get the updated state. TODO: Make updates to state only by accessor-functions. Then remove this.
                            
                let newFieldDecl =
                    {
                        FieldDecl.Field = field;
                        FieldDecl.Type = Type.BoolType;
                        FieldDecl.Init = [Val.BoolVal(false)] ; //TODO: semantics: a failure is always initially false
                    }
                let newReqPortDecl = 
                    {
                        ReqPortDecl.ReqPort = reqPort;
                        ReqPortDecl.Params = [];
                    }                    
                let newProvPortDecl =
                    {
                        ProvPortDecl.FaultExpr = None;
                        ProvPortDecl.ProvPort = provPort;
                        ProvPortDecl.Params = [];
                        ProvPortDecl.Behavior = faultToConvert.Step;
                    }
                let newBindingDecl = 
                    {
                        BndDecl.Target = {BndTarget.Comp = None; BndTarget.ReqPort = reqPort};
                        BndDecl.Source = {BndSrc.Comp = None; BndSrc.ProvPort = provPort};
                        BndDecl.Kind = BndKind.Instantaneous;
                    }                                
                let newCompDecl = compDecl.addField(newFieldDecl)
                                          .addReqPort(newReqPortDecl)
                                          .addProvPort(newProvPortDecl)
                                          .addBinding(newBindingDecl)
                                          .removeFault(faultToConvert)
                do! updateComponentToChange newCompDecl
                let! state = getState // To get the updated state. TODO: Make updates to state only by accessor-functions. Then remove this.
                let newConvertFaultsState =
                    { convertFaultsState with
                        ScmRewriterConvertFaults.ArtificialFaultOldToFieldNew = convertFaultsState.ArtificialFaultOldToFieldNew.Add ( (faultToConvert.Fault,field) ) ;
                        ScmRewriterConvertFaults.ArtificialFaultOldToPortNew = convertFaultsState.ArtificialFaultOldToPortNew.Add ( (faultToConvert.Fault,(newProvPortDecl.ProvPort,newReqPortDecl.ReqPort)) );
                    }
                let modifiedState =
                    { state with
                        ScmRewriteState.ConvertFaults = Some(newConvertFaultsState);
                        ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                    }                
                return! putState modifiedState
    }

    let replaceStepFaultByCallPort : ScmRewriteFunction<unit> = scmRewrite {
        let! state = getState
        if (state.ConvertFaults.IsNone) then
            return ()
        else
            let convertFaultsState = state.ConvertFaults.Value            
            if convertFaultsState.BehaviorsToRewrite.IsEmpty then
                // do not modify old tainted state here
                return ()
            else
                let! compDecl = getSubComponentToChange
                let behaviorToRewriteWithLocation = convertFaultsState.BehaviorsToRewrite.Head
                let behaviorToRewrite = behaviorToRewriteWithLocation.Behavior

                let newBehavior =
                    { behaviorToRewrite with
                        BehaviorDecl.Body = rewriteStm_stepFaultToPortCall convertFaultsState.ArtificialFaultOldToPortNew behaviorToRewrite.Body;
                    }

                match behaviorToRewriteWithLocation with
                    | BehaviorWithLocation.InProvPort (_,provPort,_) ->
                        let newProvPort =
                            { provPort with
                                ProvPortDecl.Behavior = newBehavior;
                            }
                        let newCompDecl = compDecl.replaceProvPort(provPort,newProvPort);
                        do! updateComponentToChange newCompDecl
                        let! state = getState // To get the updated state. TODO: Make updates to state only by accessor-functions. Then remove this.
                        let newConvertFaultsState =
                            { convertFaultsState with
                                ScmRewriterConvertFaults.BehaviorsToRewrite = convertFaultsState.BehaviorsToRewrite.Tail;
                            }
                        let modifiedState =
                            { state with
                                ScmRewriteState.ConvertFaults = Some(newConvertFaultsState);
                                ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                            }
                        return! putState modifiedState
                    | BehaviorWithLocation.InFault (_,fault,_) ->
                        let newFault =
                            { fault with
                                FaultDecl.Step = newBehavior;
                            }
                        let newCompDecl = compDecl.replaceFault(fault,newFault);                        
                        do! updateComponentToChange newCompDecl
                        let! state = getState // To get the updated state. TODO: Make updates to state only by accessor-functions. Then remove this.
                        let newConvertFaultsState =
                            { convertFaultsState with
                                ScmRewriterConvertFaults.BehaviorsToRewrite = convertFaultsState.BehaviorsToRewrite.Tail;
                            }
                        let modifiedState =
                            { state with
                                ScmRewriteState.ConvertFaults = Some(newConvertFaultsState);
                                ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                            }
                        return! putState modifiedState
                    | BehaviorWithLocation.InStep (_,step,_) ->
                        let newStep =
                            { step with
                                StepDecl.Behavior = newBehavior;
                            }
                        let newCompDecl = compDecl.replaceStep(step,newStep);                        
                        do! updateComponentToChange newCompDecl
                        let! state = getState // To get the updated state. TODO: Make updates to state only by accessor-functions. Then remove this.
                        let newConvertFaultsState =
                            { convertFaultsState with
                                ScmRewriterConvertFaults.BehaviorsToRewrite = convertFaultsState.BehaviorsToRewrite.Tail;
                            }
                        let modifiedState =
                            { state with
                                ScmRewriteState.ConvertFaults = Some(newConvertFaultsState);
                                ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                            }
                        return! putState modifiedState
    }

    

    let uniteProvPortDecls  : ScmRewriteFunction<unit> = scmRewrite {
        //for each ProvPort: replace all ProvPortDecls with the same ProvPort with one ProvPortDecl: Make a guarded command, which differentiates between the different faults
        let! state = getState
        if (state.ConvertFaults.IsNone) then
            return ()
        else
            let convertFaultsState = state.ConvertFaults.Value
            let! compDecl = getSubComponentToChange

            // TODO: Assume semantics:
            //     - For every ProvPort, _exactly_ 1 ProvPortDecl without FaultExpr exists
            
            let provPortDecls = compDecl.ProvPorts

            let provPortToUniteCandidates =
                provPortDecls |> List.filter (fun provPortDecl -> provPortDecl.FaultExpr <> None)
            
            if provPortToUniteCandidates.IsEmpty then
                return ()
            else
                let provPortToUnite =
                    // Take the first Candidate
                    provPortToUniteCandidates.Head.ProvPort
                let provPortDeclsToUnite =
                    provPortDecls |> List.filter (fun provPortDecl -> provPortDecl.ProvPort = provPortToUnite)
                let provPortDeclWithNominalBehavior =
                    let provPortDecl =
                        provPortDeclsToUnite |> List.filter (fun provPortDecl -> provPortDecl.FaultExpr = None)
                    provPortDecl.Head //must exist, see assumption
                let provPortDeclsWithErrorBehavior =
                    provPortDeclsToUnite |> List.filter (fun provPortDecl -> provPortDecl.FaultExpr <> None)
                let unitedVars =
                    provPortDeclsToUnite |> List.collect (fun provPortDecl -> provPortDecl.Behavior.Locals)
                                         |> Set.ofList //to remove double entries
                                         |> Set.toList
                let guardStmTuplesOfErrorBehaviors =
                    provPortDeclsWithErrorBehavior
                        |> List.map (fun provPortDecl ->
                                        let faultExprAsExpr =
                                            provPortDecl.FaultExpr.Value.rewrite_toExpr convertFaultsState.ArtificialFaultOldToFieldNew
                                        (faultExprAsExpr,provPortDecl.Behavior.Body)
                                    )
                let guardStmTupleOfNominalBehavior =
                    let elseGuard =
                        let (errorBehaviorGuards,_) = guardStmTuplesOfErrorBehaviors |> List.unzip
                        let oredErrorBehaviorGuards = Expr.createOredExpr errorBehaviorGuards
                        Expr.UExpr(oredErrorBehaviorGuards,UOp.Not)
                    (elseGuard,provPortDeclWithNominalBehavior.Behavior.Body)
                
                let guardedCommand =
                    Stm.Choice(guardStmTupleOfNominalBehavior::guardStmTuplesOfErrorBehaviors)                
                let newBehavior =
                    {
                        BehaviorDecl.Locals = unitedVars;
                        BehaviorDecl.Body = guardedCommand;
                    }
                let newProvPort =
                    { provPortDeclWithNominalBehavior with
                        ProvPortDecl.Behavior = newBehavior;
                    }
                let newCompDecl =
                    compDecl.removeProvPorts(provPortDeclsToUnite)
                            .addProvPort(newProvPort)
                do! updateComponentToChange newCompDecl
    }    
    
    let uniteStep : ScmRewriteFunction<unit> = scmRewrite {
          //for each StepDecl: replace all StepDecls one StepDecl: Make a guarded command, which differentiates between the different faults
        let! state = getState
        if (state.ConvertFaults.IsNone) then
            return ()
        else
            let convertFaultsState = state.ConvertFaults.Value
            let! compDecl = getSubComponentToChange
            
            // TODO: Assume semantics:
            //     - _exactly_ 1 Step without FaultExpr exists
            let needToUnite =
                if compDecl.Steps.Length > 1 then
                    true
                else if compDecl.Steps.Length = 0 then
                    failwith "BUG: CompDecl needs at least one step"
                else
                    false
            if (needToUnite=false) then
                // nothing to do
                return ()
            else
                // now almost 1:1 copy of uniteProvPortDecls
                let stepDecls = compDecl.Steps
                let stepDeclWithNominalBehavior =
                    let stepDecl =
                        stepDecls |> List.filter (fun stepDecl -> stepDecl.FaultExpr = None)
                    stepDecl.Head //must exist, see assumption
                let stepDeclsWithErrorBehavior =
                    stepDecls |> List.filter (fun stepDecl -> stepDecl.FaultExpr <> None)
                let unitedVars =
                    stepDecls |> List.collect (fun stepDecl -> stepDecl.Behavior.Locals)
                              |> Set.ofList //to remove double entries
                              |> Set.toList
                let guardStmTuplesOfErrorBehaviors =
                    stepDeclsWithErrorBehavior
                        |> List.map (fun stepDecl ->
                                        let faultExprAsExpr =
                                            stepDecl.FaultExpr.Value.rewrite_toExpr convertFaultsState.ArtificialFaultOldToFieldNew
                                        (faultExprAsExpr,stepDecl.Behavior.Body)
                                    )
                let guardStmTupleOfNominalBehavior =
                    let elseGuard =
                        let (errorBehaviorGuards,_) = guardStmTuplesOfErrorBehaviors |> List.unzip
                        let oredErrorBehaviorGuards = Expr.createOredExpr errorBehaviorGuards
                        Expr.UExpr(oredErrorBehaviorGuards,UOp.Not)
                    (elseGuard,stepDeclWithNominalBehavior.Behavior.Body)
                
                let guardedCommand =
                    Stm.Choice(guardStmTupleOfNominalBehavior::guardStmTuplesOfErrorBehaviors)                
                let newBehavior =
                    {
                        BehaviorDecl.Locals = unitedVars;
                        BehaviorDecl.Body = guardedCommand;
                    }
                let newStep =
                    { stepDeclWithNominalBehavior with
                        StepDecl.Behavior = newBehavior;
                    }
                let newCompDecl =
                    compDecl.removeSteps(stepDecls)
                            .addStep(newStep)
                
                do! updateComponentToChange newCompDecl
    }
    
    let convertFaultsWriteBackChangesIntoModel  : ScmRewriteFunction<unit> = scmRewrite {
        let! state = getState
        if (state.ConvertFaults.IsNone) then
            return ()
        else
            let! compDecl = getSubComponentToChange
            let convertFaultsState = state.ConvertFaults.Value
            let newModel = state.Model.replaceDescendant state.PathOfChangingSubcomponent compDecl
            let modifiedState =
                { state with
                    ScmRewriteState.ChangingSubComponent = newModel;
                    ScmRewriteState.PathOfChangingSubcomponent = [newModel.Comp];
                    ScmRewriteState.Model = newModel;
                    ScmRewriteState.ConvertFaults = None;
                    ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                }
            return! putState modifiedState
    }
       
    
    let convertFaults : ScmRewriteFunction<unit> = scmRewrite {        
        do! selectRootComponentForConvertingFaults
        do! (iterateToFixpoint replaceFaultByPortsAndFields)
        do! (iterateToFixpoint replaceStepFaultByCallPort)
        do! (iterateToFixpoint uniteProvPortDecls)
        do! uniteStep
        do! convertFaultsWriteBackChangesIntoModel
    }
