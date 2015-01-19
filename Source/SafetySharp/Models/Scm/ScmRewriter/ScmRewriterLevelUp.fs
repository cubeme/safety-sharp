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

module internal ScmRewriterLevelUp =
    open ScmHelpers
    open ScmRewriterBase

    
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Leveling up
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    let selectSubComponentForLevelingUp : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            if (state.LevelUp.IsSome) then
                // do not modify old tainted state here
                return ()
            else
                if state.Model.Subs = [] then
                // nothing to do, we are done
                    return ()
                else
                    // find component with no subcomponent, which is not the root. there must exist at least one
                    let rec findLeaf (parentPath:CompPath) (node:CompDecl) : CompPath =
                        let nodePath = node.Comp::parentPath
                        if node.Subs=[] then
                            nodePath
                        else
                            let firstChild = node.Subs.Head
                            findLeaf nodePath firstChild
                    let leaf = findLeaf ([]) (state.Model)
                    let selectedComponent = ScmRewriterLevelUp.createEmptyFromPath state.Model leaf
                    let modifiedState =
                        { state with
                            ScmRewriteState.LevelUp = Some(selectedComponent);       
                        }
                    return! putState modifiedState
        }

    let levelUpField : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.LevelUp.Value
                // parent is target, child is source
                if infos.ChildCompDecl.Fields.IsEmpty then
                    // do not modify old tainted state here
                    return! putState state
                else
                    let fieldDecl = infos.ChildCompDecl.Fields.Head
                    let field = fieldDecl.Field
                    let newChildCompDecl = infos.ChildCompDecl.removeField fieldDecl
                    let! transformedField = getUnusedFieldName (sprintf "%s_%s" infos.ChildCompDecl.getName field.getName)
                    let! state = getState // To get the updated state. TODO: Make updates to state only by accessor-functions. Then remove this.
                    let transformedFieldDecl = 
                        {fieldDecl with
                            FieldDecl.Field = transformedField;
                        }                    
                    let newParentCompDecl = infos.ParentCompDecl.replaceChild(infos.ChildCompDecl,newChildCompDecl)
                                                                .addField(transformedFieldDecl)
                    let newLevelUp =
                        { infos with
                            ScmRewriterLevelUp.ChildCompDecl = newChildCompDecl;
                            ScmRewriterLevelUp.ParentCompDecl = newParentCompDecl;
                            ScmRewriterLevelUp.ArtificialFieldsOldToNew = infos.ArtificialFieldsOldToNew.Add( field,transformedField );
                            ScmRewriterLevelUp.ArtificialFieldsNewToOld = infos.ArtificialFieldsNewToOld.Add( (infos.ParentPath,transformedField), (infos.ChildPath,field) );
                        }
                    let modifiedState =
                        { state with
                            ScmRewriteState.LevelUp = Some(newLevelUp);
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
        }
    let levelUpFault : ScmRewriteFunction<unit> = scmRewrite {
            // TODO: No example and no test, yet
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.LevelUp.Value
                // parent is target, child is source
                if infos.ChildCompDecl.Faults.IsEmpty then
                    // do not modify old tainted state here
                    return! putState state
                else
                    let faultDecl = infos.ChildCompDecl.Faults.Head
                    let fault = faultDecl.Fault
                    let newChildCompDecl = infos.ChildCompDecl.removeFault faultDecl
                    let! transformedFault = getUnusedFaultName (sprintf "%s_%s" infos.ChildCompDecl.getName fault.getName)
                    let! state = getState // To get the updated state. TODO: Make updates to state only by accessor-functions. Then remove this.
                    let transformedFaultDecl = 
                        {faultDecl with
                            FaultDecl.Fault = transformedFault;
                        }                    
                    let newParentCompDecl = infos.ParentCompDecl.replaceChild(infos.ChildCompDecl,newChildCompDecl)
                                                                .addFault(transformedFaultDecl)
                    let newLevelUp =
                        { infos with
                            ScmRewriterLevelUp.ChildCompDecl = newChildCompDecl;
                            ScmRewriterLevelUp.ParentCompDecl = newParentCompDecl;
                            ScmRewriterLevelUp.ArtificialFaultsOldToNew = infos.ArtificialFaultsOldToNew.Add( fault,transformedFault );
                            ScmRewriterLevelUp.ArtificialFaultsNewToOld = infos.ArtificialFaultsNewToOld.Add( (infos.ParentPath,transformedFault), (infos.ChildPath,fault) );
                            ScmRewriterLevelUp.FaultsToRewrite = transformedFaultDecl::infos.FaultsToRewrite;
                        }
                    let modifiedState =
                        { state with
                            ScmRewriteState.LevelUp = Some(newLevelUp);
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
        }
    let levelUpReqPort : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.LevelUp.Value
                // parent is target, child is source
                if infos.ChildCompDecl.ReqPorts.IsEmpty then
                    // do not modify old tainted state here
                    return! putState state
                else
                    let reqPortDecl = infos.ChildCompDecl.ReqPorts.Head
                    let reqPort = reqPortDecl.ReqPort
                    let newChildCompDecl = infos.ChildCompDecl.removeReqPort reqPortDecl
                    let! transformedReqPort = getUnusedReqPortName (sprintf "%s_%s" infos.ChildCompDecl.getName reqPort.getName)
                    let! state = getState // To get the updated state. TODO: Make updates to state only by accessor-functions. Then remove this.
                    let transformedReqPortDecl = 
                        {reqPortDecl with
                            ReqPortDecl.ReqPort = transformedReqPort;
                        }                    
                    let newParentCompDecl = infos.ParentCompDecl.replaceChild(infos.ChildCompDecl,newChildCompDecl)
                                                                .addReqPort(transformedReqPortDecl)
                    let newLevelUp =
                        { infos with
                            ScmRewriterLevelUp.ChildCompDecl = newChildCompDecl;
                            ScmRewriterLevelUp.ParentCompDecl = newParentCompDecl;
                            ScmRewriterLevelUp.ArtificialReqPortOldToNew = infos.ArtificialReqPortOldToNew.Add( reqPort,transformedReqPort );
                            ScmRewriterLevelUp.ArtificialReqPortNewToOld = infos.ArtificialReqPortNewToOld.Add( (infos.ParentPath,transformedReqPort), (infos.ChildPath,reqPort) );
                        }
                    let modifiedState =
                        { state with
                            ScmRewriteState.LevelUp = Some(newLevelUp);
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
        }
    let levelUpProvPort : ScmRewriteFunction<unit> = scmRewrite {            
            let getUnusedProvPortNameIfNotInMap (oldProv:ProvPort) (basedOn:string) : ScmRewriteFunction<ProvPort> = 
                let getUnusedProvPortNameIfNotInMap (state) : (ProvPort * ScmRewriteState) =
                    if state.LevelUp.Value.ArtificialProvPortOldToNew.ContainsKey oldProv then
                        (state.LevelUp.Value.ArtificialProvPortOldToNew.Item oldProv,state)
                    else
                        runState (getUnusedProvPortName basedOn) state
                ScmRewriteFunction (getUnusedProvPortNameIfNotInMap)
            
            
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.LevelUp.Value
                // parent is target, child is source
                if infos.ChildCompDecl.ProvPorts.IsEmpty then
                    // do not modify old tainted state here
                    return! putState state
                else
                    /// Note:
                    //    If a provided port with the same name was already leveled up, reuse this name.
                    //    The names after leveling up should be the same in this case!
                    
                    let provPortDecl = infos.ChildCompDecl.ProvPorts.Head
                    let provPort = provPortDecl.ProvPort
                    let newChildCompDecl = infos.ChildCompDecl.removeProvPort provPortDecl
                    
                    let! transformedProvPort = getUnusedProvPortNameIfNotInMap provPort (sprintf "%s_%s" infos.ChildCompDecl.getName provPort.getName)
                    let! state = getState // To get the updated state. TODO: Make updates to state only by accessor-functions. Then remove this.
                    let transformedProvPortDecl = 
                        {provPortDecl with
                            ProvPortDecl.ProvPort = transformedProvPort;
                        }                    
                    let newParentCompDecl = infos.ParentCompDecl.replaceChild(infos.ChildCompDecl,newChildCompDecl)
                                                                .addProvPort(transformedProvPortDecl)
                    let newLevelUp =
                        { infos with
                            ScmRewriterLevelUp.ChildCompDecl = newChildCompDecl;
                            ScmRewriterLevelUp.ParentCompDecl = newParentCompDecl;
                            ScmRewriterLevelUp.ArtificialProvPortOldToNew = infos.ArtificialProvPortOldToNew.Add( provPort,transformedProvPort );
                            ScmRewriterLevelUp.ArtificialProvPortNewToOld = infos.ArtificialProvPortNewToOld.Add( (infos.ParentPath,transformedProvPort), (infos.ChildPath,provPort) );
                            ScmRewriterLevelUp.ProvPortsToRewrite = transformedProvPortDecl::infos.ProvPortsToRewrite;
                        }
                    let modifiedState =
                        { state with
                            ScmRewriteState.LevelUp = Some(newLevelUp);
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
        }
       
    let levelUpAndRewriteBindingDeclaredInChild : ScmRewriteFunction<unit> = scmRewrite {
            // Cases: (view from parent, where sub1 is selected)                    
            //   Declared in parent (done in rule rewriteBindingDeclaredInParent)
            //    - x      -> x      (nothing to do)
            //    - x      -> sub1.x (target)
            //    - x      -> sub2.x (nothing to do)
            //    - sub1.x -> x      (source)
            //    - sub1.x -> sub1.x (source and target)
            //    - sub1.x -> sub2.x (source)
            //    - sub2.x -> x      (nothing to do)
            //    - sub2.x -> sub1.x (target)
            //    - sub2.x -> sub2.x (nothing to do)
            //   Declared in child (done here)
            //    - sub1.x -> sub1.x (source and target)
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.LevelUp.Value
                // parent is target, child is source
                if infos.ChildCompDecl.Bindings.IsEmpty then
                    // do not modify old tainted state here
                    return! putState state
                else
                    let bindingDecl = infos.ChildCompDecl.Bindings.Head
                    assert (bindingDecl.Source.Comp = None) //because the subcomponent has itself no subcomponent (we chose it so), it cannot have a binding from a subcomponent
                    assert (bindingDecl.Target.Comp = None) //because the subcomponent has itself no subcomponent (we chose it so), it cannot have a binding to a subcomponent
                    let newChildCompDecl = infos.ChildCompDecl.removeBinding bindingDecl
                    let newTarget =
                        let newReqPort = infos.ArtificialReqPortOldToNew.Item (bindingDecl.Target.ReqPort)
                        {
                            BndTarget.Comp = None;
                            BndTarget.ReqPort = newReqPort;
                        }
                    let newSource =
                        let newProvPort = infos.ArtificialProvPortOldToNew.Item (bindingDecl.Source.ProvPort)
                        {
                            BndSrc.Comp = None;
                            BndSrc.ProvPort = newProvPort;
                        }                    
                    let transformedBinding = 
                        {
                            BndDecl.Target = newTarget;
                            BndDecl.Source = newSource;
                            BndDecl.Kind = bindingDecl.Kind;
                        }                    
                    
                    let newParentCompDecl = infos.ParentCompDecl.replaceChild(infos.ChildCompDecl,newChildCompDecl)
                                                                .addBinding(transformedBinding)
                    let newLevelUp =
                        { infos with
                            ScmRewriterLevelUp.ChildCompDecl = newChildCompDecl;
                            ScmRewriterLevelUp.ParentCompDecl = newParentCompDecl;
                        }
                    let modifiedState =
                        { state with
                            ScmRewriteState.LevelUp = Some(newLevelUp);
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
        }
       
    let rewriteBindingDeclaredInParent : ScmRewriteFunction<unit> = scmRewrite {
            // Cases: (view from parent, where sub1 is selected)                    
            //   Declared in parent (done here)
            //    - x      -> x      (nothing to do)
            //    - x      -> sub1.x (target)
            //    - x      -> sub2.x (nothing to do)
            //    - sub1.x -> x      (source)
            //    - sub1.x -> sub1.x (source and target)
            //    - sub1.x -> sub2.x (source)
            //    - sub2.x -> x      (nothing to do)
            //    - sub2.x -> sub1.x (target)
            //    - sub2.x -> sub2.x (nothing to do)
            //   Declared in child (done in rule levelUpAndRewriteBindingDeclaredInChild)
            //    - sub1.x -> sub1.x (source and target)
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.LevelUp.Value
                // parent is target, child is source
                let bindingToRewrite : BndDecl option =
                    let targetIsChild (bndDecl:BndDecl) =
                        match bndDecl.Target.Comp with
                            | None -> false
                            | Some (comp) -> comp = infos.ChildCompDecl.Comp
                    let sourceIsChild (bndDecl:BndDecl) =
                        match bndDecl.Source.Comp with
                            | None -> false
                            | Some (comp) -> comp = infos.ChildCompDecl.Comp
                    infos.ParentCompDecl.Bindings |> List.tryFind (fun bndDecl -> (targetIsChild bndDecl) || (sourceIsChild bndDecl) )
                if bindingToRewrite.IsNone then
                    // do not modify old tainted state here
                    return! putState state
                else
                    let bindingToRewrite = bindingToRewrite.Value
                    
                    let newSource =
                        match bindingToRewrite.Source.Comp with
                            | None -> bindingToRewrite.Source
                            | Some (comp) ->
                                if comp = infos.ChildCompDecl.Comp then
                                    let port = infos.ArtificialProvPortOldToNew.Item (bindingToRewrite.Source.ProvPort)
                                    {
                                        BndSrc.Comp = None;
                                        BndSrc.ProvPort = port
                                    }
                                else
                                    bindingToRewrite.Source
                    let newTarget =
                        match bindingToRewrite.Target.Comp with
                            | None -> bindingToRewrite.Target
                            | Some (comp) ->
                                if comp = infos.ChildCompDecl.Comp then
                                    let port = infos.ArtificialReqPortOldToNew.Item (bindingToRewrite.Target.ReqPort)
                                    {
                                        BndTarget.Comp = None;
                                        BndTarget.ReqPort = port
                                    }
                                else
                                    bindingToRewrite.Target
                    let transformedBinding = 
                        {
                            BndDecl.Target = newTarget;
                            BndDecl.Source = newSource;
                            BndDecl.Kind = bindingToRewrite.Kind;
                        }
                    let newParentCompDecl = infos.ParentCompDecl.replaceBinding(bindingToRewrite,transformedBinding)
                    let newLevelUp =
                        { infos with
                            ScmRewriterLevelUp.ParentCompDecl = newParentCompDecl;
                            //Note: Child really stayed the same
                        }
                    let modifiedState =
                        { state with
                            ScmRewriteState.LevelUp = Some(newLevelUp);
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
        }

    let convertStepToPort : ScmRewriteFunction<unit> = scmRewrite {
            let createArtificialStep : ScmRewriteFunction<unit> = scmRewrite {
                let! state = getState
                if (state.LevelUp.IsNone) then
                    // do not modify old tainted state here
                    return! putState state // (alternative is to "return ()"
                else
                    let infos = state.LevelUp.Value
                    if infos.ChildCompDecl.Steps.IsEmpty then
                        // do not modify old tainted state here
                        return! putState state
                    else
                        if infos.ArtificialStep = None then
                            let! reqPort = getUnusedReqPortName  (sprintf "%s_step_req" infos.ChildCompDecl.Comp.getName)
                            let! provPort = getUnusedProvPortName (sprintf "%s_step_prov" infos.ChildCompDecl.Comp.getName)
                            let! state = getState // To get the updated state. TODO: Make updates to state only by accessor-functions. Then remove this.
                            
                            let newReqPortDecl = 
                                {
                                    ReqPortDecl.ReqPort = reqPort;
                                    ReqPortDecl.Params = [];
                                }
                            let newBindingDecl = 
                                {
                                    BndDecl.Target = {BndTarget.Comp = None; BndTarget.ReqPort = reqPort};
                                    BndDecl.Source = {BndSrc.Comp = None; BndSrc.ProvPort = provPort};
                                    BndDecl.Kind = BndKind.Instantaneous;
                                }
                                
                            let newChildCompDecl = infos.ChildCompDecl.addReqPort(newReqPortDecl)
                                                                      .addBinding(newBindingDecl)
                            let newParentCompDecl = infos.ParentCompDecl.replaceChild(infos.ChildCompDecl,newChildCompDecl)
                            let newInfos =
                                { infos with
                                    ScmRewriterLevelUp.ChildCompDecl = newChildCompDecl;
                                    ScmRewriterLevelUp.ParentCompDecl = newParentCompDecl;
                                    ScmRewriterLevelUp.ArtificialStep = Some((reqPort,provPort))
                                }
                            let modifiedState =
                                { state with
                                    ScmRewriteState.LevelUp = Some(newInfos);
                                    ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                                }
                            return! putState modifiedState
                        else
                            //If we already have an artificial name, use it and do not generate a binding and a reqport
                            return ()
            }
            do! createArtificialStep
            
            // replace step to required port and provided port and binding, add a link from subcomponent path to new required port
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.LevelUp.Value
                if infos.ChildCompDecl.Steps.IsEmpty then
                    // do not modify old tainted state here
                    return! putState state
                else
                    let (reqPort,provPort) = infos.ArtificialStep.Value

                    let stepToConvert = infos.ChildCompDecl.Steps.Head
                    let newProvPortDecl =
                        {
                            ProvPortDecl.FaultExpr = stepToConvert.FaultExpr;
                            ProvPortDecl.ProvPort = provPort;
                            ProvPortDecl.Params = [];
                            ProvPortDecl.Behavior = stepToConvert.Behavior;
                        }
                    let newChildCompDecl = infos.ChildCompDecl.removeStep(stepToConvert)
                                                              .addProvPort(newProvPortDecl)
                    let newParentCompDecl = infos.ParentCompDecl.replaceChild(infos.ChildCompDecl,newChildCompDecl)

                    let newLevelUp =
                        { infos with
                            ScmRewriterLevelUp.ChildCompDecl = newChildCompDecl;
                            ScmRewriterLevelUp.ParentCompDecl = newParentCompDecl;
                            ScmRewriterLevelUp.ProvPortsToRewrite = (newProvPortDecl)::infos.ProvPortsToRewrite;
                            ScmRewriterLevelUp.StepsToRewrite = infos.ParentCompDecl.Steps; //It is necessary to set this once. But it seems, that it does not harm to set it multiple times
                        }
                    let modifiedState =
                        { state with
                            ScmRewriteState.LevelUp = Some(newLevelUp);
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
                        
        }

    let rewriteParentStep : ScmRewriteFunction<unit> = scmRewrite {
            // here, additionally instead of "step subcomponent" the converted step must be called
            
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else if state.LevelUp.Value.ArtificialStep.IsNone then
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.LevelUp.Value
                
                if infos.StepsToRewrite.IsEmpty then
                        // do not modify old tainted state here
                        return! putState state
                else
                    let stepToRewrite = infos.StepsToRewrite.Head

                    let (stepReqPortPreviouslyInChild,_) = infos.ArtificialStep.Value
                    let stepReqPortNowInParent = infos.ArtificialReqPortOldToNew.Item stepReqPortPreviouslyInChild  // port (virtual step) was leveled up before, but infos.ArtificialStep.Value was not updated yet
                
                    let rewriteStep (step:StepDecl) : StepDecl =
                        let rec rewriteStm (stm:Stm) : Stm = //TODO: Move to ScmHelpers.fs. There are already similar functions
                            match stm with
                                | Stm.Block (smnts) ->
                                    let newStmnts = smnts |> List.map rewriteStm
                                    Stm.Block(newStmnts)
                                | Stm.Choice (choices:(Expr * Stm) list) ->
                                    let newChoices = choices |> List.map (fun (expr,stm) -> (expr,rewriteStm stm) )
                                    Stm.Choice(newChoices)
                                | Stm.StepComp (comp) ->
                                    Stm.CallPort (stepReqPortNowInParent,[])
                                | _ -> stm
                        let newBehavior =
                            { step.Behavior with
                                BehaviorDecl.Body = rewriteStm step.Behavior.Body;
                            }
                        { step with
                            StepDecl.Behavior = newBehavior;
                        }

                    let newStep = rewriteStep stepToRewrite                
                    let newParentCompDecl = infos.ParentCompDecl.replaceStep(stepToRewrite,newStep);
                    let newLevelUp =
                        { infos with
                            ScmRewriterLevelUp.ParentCompDecl = newParentCompDecl;
                            ScmRewriterLevelUp.StepsToRewrite = infos.StepsToRewrite.Tail;
                        }
                    let modifiedState =
                        { state with
                            ScmRewriteState.LevelUp = Some(newLevelUp);
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState

        }

    let rewriteProvPort : ScmRewriteFunction<unit> = scmRewrite {
            // replace reqPorts and fields by their proper names, replace Fault Expressions
            
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.LevelUp.Value
                if infos.ProvPortsToRewrite.IsEmpty then
                    // do not modify old tainted state here
                    return! putState state
                else
                    // we are in a parent Component!!!
                    let provPortToRewrite = infos.ProvPortsToRewrite.Head
                    
                    let rewrittenProvPort =
                        {
                            ProvPortDecl.FaultExpr = rewriteFaultExprOption infos.oldToNewMaps2 provPortToRewrite.FaultExpr;
                            ProvPortDecl.ProvPort = provPortToRewrite.ProvPort;
                            ProvPortDecl.Params = provPortToRewrite.Params; // The getUnusedxxxName-Functions also ensured, that the names of new fields and faults,... do not overlap with any param. So we can keep it
                            ProvPortDecl.Behavior = rewriteBehavior infos.oldToNewMaps1 provPortToRewrite.Behavior;
                        }
                    let newParentCompDecl = infos.ParentCompDecl.replaceProvPort(provPortToRewrite,rewrittenProvPort)

                    let newLevelUp =
                        { infos with
                            ScmRewriterLevelUp.ParentCompDecl = newParentCompDecl;
                            ScmRewriterLevelUp.ProvPortsToRewrite = infos.ProvPortsToRewrite.Tail;
                        }
                    let modifiedState =
                        { state with
                            ScmRewriteState.LevelUp = Some(newLevelUp);
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
        }

    let rewriteFaults : ScmRewriteFunction<unit> = scmRewrite {
            // replace reqPorts and fields by their proper names, replace Fault Expressions
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.LevelUp.Value
                if infos.FaultsToRewrite.IsEmpty then
                    // do not modify old tainted state here
                    return! putState state
                else
                    // we are in a parent Component!!!
                    let faultToRewrite = infos.FaultsToRewrite.Head
                    
                    let rewrittenFault =
                        {
                            FaultDecl.Fault = faultToRewrite.Fault;
                            FaultDecl.Step = rewriteBehavior infos.oldToNewMaps1 faultToRewrite.Step;
                        }
                    let newParentCompDecl = infos.ParentCompDecl.replaceFault(faultToRewrite,rewrittenFault)

                    let newLevelUp =
                        { infos with
                            ScmRewriterLevelUp.ParentCompDecl = newParentCompDecl;
                            ScmRewriterLevelUp.FaultsToRewrite = infos.FaultsToRewrite.Tail;
                        }
                    let modifiedState =
                        { state with
                            ScmRewriteState.LevelUp = Some(newLevelUp);
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
        }
    let assertSubcomponentEmpty : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.LevelUp.Value
                assert (infos.ChildCompDecl.Subs = [])
                assert (infos.ChildCompDecl.Fields = [])
                assert (infos.ChildCompDecl.Faults = [])
                assert (infos.ChildCompDecl.ReqPorts = [])
                assert (infos.ChildCompDecl.ProvPorts = [])
                assert (infos.ChildCompDecl.Bindings = [])
                return ()
        }
    let removeSubComponent : ScmRewriteFunction<unit> = scmRewrite {            
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.LevelUp.Value
                let newParentCompDecl = infos.ParentCompDecl.removeChild(infos.ChildCompDecl)
                let newLevelUp =
                    { infos with
                        ScmRewriterLevelUp.ParentCompDecl = newParentCompDecl;
                    }
                let modifiedState =
                    { state with
                        ScmRewriteState.LevelUp = Some(newLevelUp);
                        ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                    }
                return! putState modifiedState
                
        }        
    let levelUpWriteBackChangesIntoModel  : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let levelUp = state.LevelUp.Value
                let newModel = state.Model.replaceDescendant levelUp.ParentPath levelUp.ParentCompDecl
                let modifiedState =
                    { state with
                        ScmRewriteState.Model = newModel;
                        ScmRewriteState.LevelUp = None;
                        ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                    }
                return! putState modifiedState
        }
    let assertNoSubcomponent : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            assert (state.Model.Subs=[])
            return ()
        }
        
    let levelUpSubcomponent : ScmRewriteFunction<unit> = scmRewrite {
            // idea: first level up every item of a component,
            //       then rewrite every code accessing to some specific element of it
            do! selectSubComponentForLevelingUp
            do! (iterateToFixpoint levelUpField) //Invariant: Imagine LevelUp are written back into model. Fieldaccess (read/write) is either on the "real" field or on a "forwarded field" (map entry in ArtificialFieldsOldToNew exists, and new field exists)
            do! (iterateToFixpoint levelUpFault)
            do! (iterateToFixpoint convertStepToPort)
            do! (iterateToFixpoint levelUpReqPort)
            do! (iterateToFixpoint levelUpProvPort)
            do! (iterateToFixpoint levelUpAndRewriteBindingDeclaredInChild)
            do! (iterateToFixpoint rewriteBindingDeclaredInParent)
            do! (iterateToFixpoint rewriteParentStep)
            do! (iterateToFixpoint rewriteProvPort)
            do! (iterateToFixpoint rewriteFaults)
            do! assertSubcomponentEmpty
            do! removeSubComponent
            do! levelUpWriteBackChangesIntoModel
        }
                
    let levelUpSubcomponents : ScmRewriteFunction<unit> = scmRewrite {
            do! (iterateToFixpoint levelUpSubcomponent)
    }