﻿// The MIT License (MIT)
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

module internal ScmRewriterLevelUp =
    open ScmHelpers
    open ScmRewriterBase

    
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Accessor Functions to ScmRewriterLevelUp (and ScmRewriterState
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    
    let getParentCompDecl : ScmRewriteFunction<CompDecl> = 
        ScmRewriterBase.getSubComponentToChange
        
    let updateParentCompDecl (newParent:CompDecl) : ScmRewriteFunction<unit> = 
        ScmRewriterBase.updateSubComponentToChange newParent

    let getChildCompDecl : ScmRewriteFunction<CompDecl> = 
        let getChildCompDecl (state:ScmRewriteState) : (CompDecl * ScmRewriteState) =
            let childName = state.LevelUp.Value.NameOfChildToRewrite
            let childCompDecl =
                state.ChangingSubComponent.Subs |> List.find (fun subComp -> subComp.Comp = childName)
            childCompDecl,state
        ScmRewriteFunction (getChildCompDecl)

        
    // this should be removed: Every access to levelup-State should be done by a ScmRewriteFunction
    let hasLevelUpState : ScmRewriteFunction<bool> = 
        let hasLevelUp (state:ScmRewriteState) : (bool * ScmRewriteState) =
            state.LevelUp.IsSome,state
        ScmRewriteFunction (hasLevelUp)
        
        
    // this should be removed: Every access to levelup-State should be done by a ScmRewriteFunction
    let getLevelUpState : ScmRewriteFunction<ScmRewriterLevelUp> = 
        let getLevelUpState (state:ScmRewriteState) : (ScmRewriterLevelUp * ScmRewriteState) =
            state.LevelUp.Value,state
        ScmRewriteFunction (getLevelUpState)

    // this should be removed: Every access to levelup-State should be done by a ScmRewriteFunction
    let updateLevelUpState (newLevelUp:ScmRewriterLevelUp) : ScmRewriteFunction<unit> = 
        let updateLevelUpState (state:ScmRewriteState) : (unit * ScmRewriteState) =
            let newState =
                { state with
                    ScmRewriteState.LevelUp = Some(newLevelUp);
                    ScmRewriteState.Tainted = true;
                }
            (),newState
        ScmRewriteFunction (updateLevelUpState)

    (*
    let getParentPath : ScmRewriteFunction<CompPath> = scmRewrite {
        let! state = getState
        let parentPath = state.PathOfChangingSubcomponent
        return parentPath
    }

    let getChildPath : ScmRewriteFunction<CompPath> = scmRewrite {
        let! state = getState
        let parentPath = state.PathOfChangingSubcomponent
        return state.LevelUp.Value.NameOfChildToRewrite::parentPath
    }
    *)
    
    let addArtificialField (oldField:Field) (newField:Field) : ScmRewriteFunction<unit> = scmRewrite {
        let! state = getState
        let! levelUp = getLevelUpState
        let parentPath = state.PathOfChangingSubcomponent
        let childPath = levelUp.NameOfChildToRewrite::parentPath
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUp.ArtificialFieldsOldToNew = levelUp.ArtificialFieldsOldToNew.Add( oldField,newField );
                ScmRewriterLevelUp.ArtificialFieldsNewToOld = levelUp.ArtificialFieldsNewToOld.Add( (parentPath,newField), (childPath,oldField) );
            }
        do! updateLevelUpState newLevelUp
    }

    let addArtificialFault (oldFault:Fault) (newFault:Fault) : ScmRewriteFunction<unit> = scmRewrite {
        let! state = getState
        let! levelUp = getLevelUpState
        let parentPath = state.PathOfChangingSubcomponent
        let childPath = levelUp.NameOfChildToRewrite::parentPath
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUp.ArtificialFaultsOldToNew = levelUp.ArtificialFaultsOldToNew.Add( oldFault,newFault );
                ScmRewriterLevelUp.ArtificialFaultsNewToOld = levelUp.ArtificialFaultsNewToOld.Add( (parentPath,newFault), (childPath,oldFault) );
            }
        do! updateLevelUpState newLevelUp
    }

    let addArtificialReqPort (oldReqPort:ReqPort) (newReqPort:ReqPort) : ScmRewriteFunction<unit> = scmRewrite {
        let! state = getState
        let! levelUp = getLevelUpState
        let parentPath = state.PathOfChangingSubcomponent
        let childPath = levelUp.NameOfChildToRewrite::parentPath
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUp.ArtificialReqPortOldToNew = levelUp.ArtificialReqPortOldToNew.Add( oldReqPort,newReqPort );
                ScmRewriterLevelUp.ArtificialReqPortNewToOld = levelUp.ArtificialReqPortNewToOld.Add( (parentPath,newReqPort), (childPath,oldReqPort) );
            }
        do! updateLevelUpState newLevelUp
    }

    let addArtificialProvPort (oldProvPort:ProvPort) (newProvPort:ProvPort) : ScmRewriteFunction<unit> = scmRewrite {
        let! state = getState
        let! levelUp = getLevelUpState
        let parentPath = state.PathOfChangingSubcomponent
        let childPath = levelUp.NameOfChildToRewrite::parentPath
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUp.ArtificialProvPortOldToNew = levelUp.ArtificialProvPortOldToNew.Add( oldProvPort,newProvPort );
                ScmRewriterLevelUp.ArtificialProvPortNewToOld = levelUp.ArtificialProvPortNewToOld.Add( (parentPath,newProvPort), (childPath,oldProvPort) );
            }
        do! updateLevelUpState newLevelUp
    }
    
    let popFaultToRewrite : ScmRewriteFunction<FaultDecl option> = scmRewrite {
        let! levelUp = getLevelUpState
        if levelUp.FaultsToRewrite.IsEmpty then
            return None
        else
            let faultToRewrite = levelUp.FaultsToRewrite.Head
            let newLevelUp = 
                { levelUp with
                    ScmRewriterLevelUp.FaultsToRewrite = levelUp.FaultsToRewrite.Tail;
                }
            do! updateLevelUpState newLevelUp
            return Some(faultToRewrite)
    }
    
    let popProvPortToRewrite : ScmRewriteFunction<ProvPortDecl option> = scmRewrite {
        let! levelUp = getLevelUpState
        if levelUp.ProvPortsToRewrite.IsEmpty then
            return None
        else
            let provPortToRewrite = levelUp.ProvPortsToRewrite.Head
            let newLevelUp = 
                { levelUp with
                    ScmRewriterLevelUp.ProvPortsToRewrite = levelUp.ProvPortsToRewrite.Tail;
                }
            do! updateLevelUpState newLevelUp
            return Some(provPortToRewrite)
    }

    let popStepToRewrite : ScmRewriteFunction<StepDecl option> = scmRewrite {
        let! levelUp = getLevelUpState
        if levelUp.StepsToRewrite.IsEmpty then
            return None
        else
            let stepToRewrite = levelUp.StepsToRewrite.Head
            let newLevelUp = 
                { levelUp with
                    ScmRewriterLevelUp.StepsToRewrite = levelUp.StepsToRewrite.Tail;
                }
            do! updateLevelUpState newLevelUp
            return Some(stepToRewrite)
    }

    
    let pushFaultToRewrite (faultToRewrite:FaultDecl) : ScmRewriteFunction<unit> = scmRewrite {
        let! levelUp = getLevelUpState
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUp.FaultsToRewrite = faultToRewrite::levelUp.FaultsToRewrite;
            }
        do! updateLevelUpState newLevelUp
        return ()
    }

    let pushProvPortToRewrite (provPortToRewrite:ProvPortDecl) : ScmRewriteFunction<unit> = scmRewrite {
        let! levelUp = getLevelUpState
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUp.ProvPortsToRewrite = provPortToRewrite::levelUp.ProvPortsToRewrite;
            }
        do! updateLevelUpState newLevelUp
        return ()
    }
    
    let allParentStepsShouldBeRewrittenLater : ScmRewriteFunction<unit> = scmRewrite {
        let! levelUp = getLevelUpState
        let! parentCompDecl = getParentCompDecl
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUp.StepsToRewrite = parentCompDecl.Steps;
            }
        do! updateLevelUpState newLevelUp
        return ()
    }

    
    let setArtificialStep (reqport:ReqPort,provPort:ProvPort) : ScmRewriteFunction<unit> = scmRewrite {
        let! levelUp = getLevelUpState
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUp.ArtificialStep = Some(reqport,provPort);
            }
        do! updateLevelUpState newLevelUp
        return ()
    }

    let getArtificialStep : ScmRewriteFunction<ReqPort*ProvPort> = scmRewrite {
        let! levelUp = getLevelUpState
        return levelUp.ArtificialStep.Value
    }

    (*


    let push (oldProvPort:ProvPort) (newProvPort:ProvPort) : ScmRewriteFunction<unit> = scmRewrite {
        let! levelUp = getLevelUpState
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUp.ArtificialProvPortOldToNew = levelUp.ArtificialProvPortOldToNew.Add( oldProvPort,newProvPort );
                ScmRewriterLevelUp.ArtificialProvPortNewToOld = levelUp.ArtificialProvPortNewToOld.Add( (parentPath,newProvPort), (childPath,oldProvPort) );
            }
        do! updateLevelUpState newLevelUp
    }

    *)


        
    let setChildToLevelUp (path:CompPath) : ScmRewriteFunction<unit> =
        let setChildToLevelUp (state:ScmRewriteState) : (unit * ScmRewriteState) =            
            let parentPath = path.Tail
            let parentCompDecl = state.Model.getDescendantUsingPath parentPath
            let childName = path.Head
            let newLevelUp =
                {
                    ScmRewriterLevelUp.NameOfChildToRewrite = childName;
                    ScmRewriterLevelUp.ArtificialFieldsOldToNew = Map.empty<Field,Field>;
                    ScmRewriterLevelUp.ArtificialFaultsOldToNew = Map.empty<Fault,Fault>;
                    ScmRewriterLevelUp.ArtificialReqPortOldToNew = Map.empty<ReqPort,ReqPort>;
                    ScmRewriterLevelUp.ArtificialProvPortOldToNew = Map.empty<ProvPort,ProvPort>;
                    ScmRewriterLevelUp.ArtificialFieldsNewToOld = Map.empty<FieldPath,FieldPath>;
                    ScmRewriterLevelUp.ArtificialFaultsNewToOld = Map.empty<FaultPath,FaultPath>;
                    ScmRewriterLevelUp.ArtificialReqPortNewToOld = Map.empty<ReqPortPath,ReqPortPath>;
                    ScmRewriterLevelUp.ArtificialProvPortNewToOld = Map.empty<ProvPortPath,ProvPortPath>;
                    ScmRewriterLevelUp.FaultsToRewrite = [];
                    ScmRewriterLevelUp.ProvPortsToRewrite = [];
                    ScmRewriterLevelUp.StepsToRewrite = [];
                    ScmRewriterLevelUp.ArtificialStep = None;
                }            
            let newState =
                { state with
                    ScmRewriteState.ChangingSubComponent = parentCompDecl;
                    ScmRewriteState.PathOfChangingSubcomponent = parentPath;
                    ScmRewriteState.LevelUp = Some(newLevelUp);
                    ScmRewriteState.Tainted = true;
                }
            (),newState
        ScmRewriteFunction (setChildToLevelUp) 

    
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
                    do! setChildToLevelUp leaf
                    return ()
        }

    let levelUpField : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return ()
            else
                let levelUp = state.LevelUp.Value
                // parent is target, child is source
                let! childCompDecl = getChildCompDecl
                let! parentCompDecl = getParentCompDecl

                if childCompDecl.Fields.IsEmpty then
                    // do not modify old tainted state here
                    return ()
                else
                    let fieldDecl = childCompDecl.Fields.Head
                    let field = fieldDecl.Field
                    let newChildCompDecl = childCompDecl.removeField fieldDecl
                    let! transformedField = getUnusedFieldName (sprintf "%s_%s" childCompDecl.getName field.getName)
                    
                    let transformedFieldDecl = 
                        {fieldDecl with
                            FieldDecl.Field = transformedField;
                        }                    
                    let newParentCompDecl = parentCompDecl.replaceChild(childCompDecl,newChildCompDecl)
                                                          .addField(transformedFieldDecl)
                    do! updateParentCompDecl newParentCompDecl
                    do! addArtificialField field transformedField
        }
    let levelUpFault : ScmRewriteFunction<unit> = scmRewrite {
            // TODO: No example and no test, yet
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return ()
            else
                let levelUp = state.LevelUp.Value
                // parent is target, child is source
                let! childCompDecl = getChildCompDecl
                let! parentCompDecl = getParentCompDecl
                if childCompDecl.Faults.IsEmpty then
                    // do not modify old tainted state here
                    return ()
                else
                    let faultDecl = childCompDecl.Faults.Head
                    let fault = faultDecl.Fault
                    let newChildCompDecl = childCompDecl.removeFault faultDecl
                    let! transformedFault = getUnusedFaultName (sprintf "%s_%s" childCompDecl.getName fault.getName)
                    let transformedFaultDecl = 
                        {faultDecl with
                            FaultDecl.Fault = transformedFault;
                        }                    
                    let newParentCompDecl = parentCompDecl.replaceChild(childCompDecl,newChildCompDecl)
                                                          .addFault(transformedFaultDecl)
                    do! updateParentCompDecl newParentCompDecl
                    do! addArtificialFault fault transformedFault
                    do! pushFaultToRewrite transformedFaultDecl
        }
    let levelUpReqPort : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return ()
            else
                let levelUp = state.LevelUp.Value
                // parent is target, child is source
                let! childCompDecl = getChildCompDecl
                let! parentCompDecl = getParentCompDecl

                if childCompDecl.ReqPorts.IsEmpty then
                    // do not modify old tainted state here
                    return! putState state
                else
                    let reqPortDecl = childCompDecl.ReqPorts.Head
                    let reqPort = reqPortDecl.ReqPort
                    let newChildCompDecl = childCompDecl.removeReqPort reqPortDecl
                    let! transformedReqPort = getUnusedReqPortName (sprintf "%s_%s" childCompDecl.getName reqPort.getName)
                    let transformedReqPortDecl = 
                        {reqPortDecl with
                            ReqPortDecl.ReqPort = transformedReqPort;
                        }                    
                    let newParentCompDecl = parentCompDecl.replaceChild(childCompDecl,newChildCompDecl)
                                                          .addReqPort(transformedReqPortDecl)
                    do! updateParentCompDecl newParentCompDecl
                    do! addArtificialReqPort reqPort transformedReqPort
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
                return ()
            else
                let levelUp = state.LevelUp.Value
                // parent is target, child is source
                let! childCompDecl = getChildCompDecl
                let! parentCompDecl = getParentCompDecl

                if childCompDecl.ProvPorts.IsEmpty then
                    // do not modify old tainted state here
                    return ()
                else
                    /// Note:
                    //    If a provided port with the same name was already leveled up, reuse this name.
                    //    The names after leveling up should be the same in this case!
                    
                    let provPortDecl = childCompDecl.ProvPorts.Head
                    let provPort = provPortDecl.ProvPort
                    let newChildCompDecl = childCompDecl.removeProvPort provPortDecl
                    
                    let! transformedProvPort = getUnusedProvPortNameIfNotInMap provPort (sprintf "%s_%s" childCompDecl.getName provPort.getName)
                    let transformedProvPortDecl = 
                        {provPortDecl with
                            ProvPortDecl.ProvPort = transformedProvPort;
                        }                    
                    let newParentCompDecl = parentCompDecl.replaceChild(childCompDecl,newChildCompDecl)
                                                          .addProvPort(transformedProvPortDecl)
                    do! updateParentCompDecl newParentCompDecl
                    do! addArtificialProvPort provPort transformedProvPort
                    do! pushProvPortToRewrite transformedProvPortDecl
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
                return ()
            else
                let levelUp = state.LevelUp.Value
                // parent is target, child is source
                let! childCompDecl = getChildCompDecl
                let! parentCompDecl = getParentCompDecl

                if childCompDecl.Bindings.IsEmpty then
                    // do not modify old tainted state here
                    return ()
                else
                    let bindingDecl = childCompDecl.Bindings.Head
                    assert (bindingDecl.Source.Comp = None) //because the subcomponent has itself no subcomponent (we chose it so), it cannot have a binding from a subcomponent
                    assert (bindingDecl.Target.Comp = None) //because the subcomponent has itself no subcomponent (we chose it so), it cannot have a binding to a subcomponent
                    let newChildCompDecl = childCompDecl.removeBinding bindingDecl
                    let newTarget =
                        let newReqPort = levelUp.ArtificialReqPortOldToNew.Item (bindingDecl.Target.ReqPort)
                        {
                            BndTarget.Comp = None;
                            BndTarget.ReqPort = newReqPort;
                        }
                    let newSource =
                        let newProvPort = levelUp.ArtificialProvPortOldToNew.Item (bindingDecl.Source.ProvPort)
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
                    
                    let newParentCompDecl = parentCompDecl.replaceChild(childCompDecl,newChildCompDecl)
                                                          .addBinding(transformedBinding)
                    do! updateParentCompDecl newParentCompDecl
                    return ()
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
                let levelUp = state.LevelUp.Value
                // parent is target, child is source
                let! childCompDecl = getChildCompDecl
                let! parentCompDecl = getParentCompDecl


                let bindingToRewrite : BndDecl option =
                    let targetIsChild (bndDecl:BndDecl) =
                        match bndDecl.Target.Comp with
                            | None -> false
                            | Some (comp) -> comp = childCompDecl.Comp
                    let sourceIsChild (bndDecl:BndDecl) =
                        match bndDecl.Source.Comp with
                            | None -> false
                            | Some (comp) -> comp = childCompDecl.Comp
                    parentCompDecl.Bindings |> List.tryFind (fun bndDecl -> (targetIsChild bndDecl) || (sourceIsChild bndDecl) )
                if bindingToRewrite.IsNone then
                    // do not modify old tainted state here
                    return! putState state
                else
                    let bindingToRewrite = bindingToRewrite.Value
                    
                    let newSource =
                        match bindingToRewrite.Source.Comp with
                            | None -> bindingToRewrite.Source
                            | Some (comp) ->
                                if comp = childCompDecl.Comp then
                                    let port = levelUp.ArtificialProvPortOldToNew.Item (bindingToRewrite.Source.ProvPort)
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
                                if comp = childCompDecl.Comp then
                                    let port = levelUp.ArtificialReqPortOldToNew.Item (bindingToRewrite.Target.ReqPort)
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
                    let newParentCompDecl = parentCompDecl.replaceBinding(bindingToRewrite,transformedBinding)
                    do! updateParentCompDecl newParentCompDecl
        }

        
    let createArtificialStep : ScmRewriteFunction<unit> = scmRewrite {
        let! state = getState
        if (state.LevelUp.IsNone) then
            // do not modify old tainted state here
            return! putState state // (alternative is to "return ()"
        else
            let levelUp = state.LevelUp.Value
            // parent is target, child is source
            let! childCompDecl = getChildCompDecl
            let! parentCompDecl = getParentCompDecl


            if childCompDecl.Steps.IsEmpty then
                // do not modify old tainted state here
                return! putState state
            else
                if levelUp.ArtificialStep = None then
                    let! reqPort = getUnusedReqPortName  (sprintf "%s_step_req" childCompDecl.Comp.getName)
                    let! provPort = getUnusedProvPortName (sprintf "%s_step_prov" childCompDecl.Comp.getName)
                            
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
                                
                    let newChildCompDecl = childCompDecl.addReqPort(newReqPortDecl)
                                                        .addBinding(newBindingDecl)
                    let newParentCompDecl = parentCompDecl.replaceChild(childCompDecl,newChildCompDecl)
                    do! updateParentCompDecl newParentCompDecl
                    do! setArtificialStep (reqPort,provPort)                            
                else
                    //If we already have an artificial name, use it and do not generate a binding and a reqport
                    return ()
    }


    let convertStepToPort : ScmRewriteFunction<unit> = scmRewrite {
            do! createArtificialStep
            
            // replace step to required port and provided port and binding, add a link from subcomponent path to new required port
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return ()
            else
                let levelUp = state.LevelUp.Value
                // parent is target, child is source
                let! childCompDecl = getChildCompDecl
                let! parentCompDecl = getParentCompDecl
                if childCompDecl.Steps.IsEmpty then
                    // do not modify old tainted state here
                    return ()
                else
                    let! (reqPort,provPort) = getArtificialStep

                    let stepToConvert = childCompDecl.Steps.Head
                    let newProvPortDecl =
                        {
                            ProvPortDecl.FaultExpr = stepToConvert.FaultExpr;
                            ProvPortDecl.ProvPort = provPort;
                            ProvPortDecl.Params = [];
                            ProvPortDecl.Behavior = stepToConvert.Behavior;
                        }
                    let newChildCompDecl = childCompDecl.removeStep(stepToConvert)
                                                              .addProvPort(newProvPortDecl)
                    let newParentCompDecl = parentCompDecl.replaceChild(childCompDecl,newChildCompDecl)
                    
                    do! updateParentCompDecl newParentCompDecl
                    do! allParentStepsShouldBeRewrittenLater // all parent steps need to be rewritten later. The step comp must be replaced by the new reqport-call
                    do! pushProvPortToRewrite newProvPortDecl
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
                let levelUp = state.LevelUp.Value
                let! parentCompDecl = getParentCompDecl
                             
                let! stepToRewrite = popStepToRewrite
                                
                match stepToRewrite with
                    | None ->
                        // do not modify old tainted state here
                        return()
                    | Some(stepToRewrite) ->
                        let (stepReqPortPreviouslyInChild,_) = levelUp.ArtificialStep.Value
                        let stepReqPortNowInParent = levelUp.ArtificialReqPortOldToNew.Item stepReqPortPreviouslyInChild  // port (virtual step) was leveled up before, but levelUp.ArtificialStep.Value was not updated yet
                
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
                        let newParentCompDecl = parentCompDecl.replaceStep(stepToRewrite,newStep);                    
                        do! updateParentCompDecl newParentCompDecl
        }

    let rewriteProvPort : ScmRewriteFunction<unit> = scmRewrite {
            // replace reqPorts and fields by their proper names, replace Fault Expressions
            
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let levelUp = state.LevelUp.Value
                let! parentCompDecl = getParentCompDecl
                                
                let! provPortToRewrite = popProvPortToRewrite
                match provPortToRewrite with
                    | None ->
                        // do not modify old tainted state here
                        return! putState state
                    | Some(provPortToRewrite) ->
                        // we are in a parent Component!!!
                        let rewrittenProvPort =
                            {
                                ProvPortDecl.FaultExpr = rewriteFaultExprOption levelUp.oldToNewMaps2 provPortToRewrite.FaultExpr;
                                ProvPortDecl.ProvPort = provPortToRewrite.ProvPort;
                                ProvPortDecl.Params = provPortToRewrite.Params; // The getUnusedxxxName-Functions also ensured, that the names of new fields and faults,... do not overlap with any param. So we can keep it
                                ProvPortDecl.Behavior = rewriteBehavior levelUp.oldToNewMaps1 provPortToRewrite.Behavior;
                            }
                        let newParentCompDecl = parentCompDecl.replaceProvPort(provPortToRewrite,rewrittenProvPort)
                        do! updateParentCompDecl newParentCompDecl                        
        }

    let rewriteFaults : ScmRewriteFunction<unit> = scmRewrite {
            // replace reqPorts and fields by their proper names, replace Fault Expressions
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return ()
            else
                let levelUp = state.LevelUp.Value
                let! parentCompDecl = getParentCompDecl
                
                let! faultToRewrite = popFaultToRewrite
                match faultToRewrite with
                    | None ->
                        // do not modify old tainted state here
                        return! putState state
                    | Some(faultToRewrite) ->
                        // we are in a parent Component!!!
                        let rewrittenFault =
                            {
                                FaultDecl.Fault = faultToRewrite.Fault;
                                FaultDecl.Step = rewriteBehavior levelUp.oldToNewMaps1 faultToRewrite.Step;
                            }
                        let newParentCompDecl = parentCompDecl.replaceFault(faultToRewrite,rewrittenFault)
                        do! updateParentCompDecl newParentCompDecl                        
        }
    let assertSubcomponentEmpty : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let levelUp = state.LevelUp.Value
                let! parentCompDecl = getParentCompDecl
                let! childCompDecl = getChildCompDecl

                assert (childCompDecl.Subs = [])
                assert (childCompDecl.Fields = [])
                assert (childCompDecl.Faults = [])
                assert (childCompDecl.ReqPorts = [])
                assert (childCompDecl.ProvPorts = [])
                assert (childCompDecl.Bindings = [])
                return ()
        }
    let removeSubComponent : ScmRewriteFunction<unit> = scmRewrite {            
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let levelUp = state.LevelUp.Value
                let! parentCompDecl = getParentCompDecl
                let! childCompDecl = getChildCompDecl
                let newParentCompDecl = parentCompDecl.removeChild(childCompDecl)
                do! updateParentCompDecl newParentCompDecl
                
        }        
    let levelUpWriteBackChangesIntoModel  : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            if (state.LevelUp.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let levelUp = state.LevelUp.Value
                let! parentCompDecl = getParentCompDecl

                let newModel = state.Model.replaceDescendant state.PathOfChangingSubcomponent parentCompDecl
                let modifiedState =
                    { state with
                        ScmRewriteState.ChangingSubComponent = newModel;
                        ScmRewriteState.PathOfChangingSubcomponent = [newModel.Comp];
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