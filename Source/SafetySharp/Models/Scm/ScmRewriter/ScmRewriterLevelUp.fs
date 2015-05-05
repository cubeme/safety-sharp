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
open SafetySharp.Models.Scm

module internal ScmRewriterLevelUp =
    open ScmHelpers
    open ScmRewriterBase
    open SafetySharp.Workflow
    open ScmMutable
    
    type ScmRewriterLevelUpState<'traceableOfOrigin> = {
        Model : ScmModel;
        UncommittedForwardTracerMap : Map<Traceable,Traceable>;
        TraceablesOfOrigin : 'traceableOfOrigin list;
        ForwardTracer : 'traceableOfOrigin -> Traceable;
        PathOfChangingSubcomponent : CompPath; //path of the Parent of the subcomponent, which gets changed
        TakenNames : Set<string>;

        // child lives in parent. Things from the child are moved
        // into the parent. The path to the parent is declared in the ScmRewriterState
        NameOfChildToRewrite : Comp option;
        
        // Forwarder
        // For each of these. Map goes from:old -> to:new. Old entity lives always in ChildPath, new in ParentPath
        // So no path is necessary
        ArtificialFieldsOldToNew : Map<Field,Field>
        ArtificialFaultsOldToNew : Map<Fault,Fault>
        ArtificialReqPortOldToNew : Map<ReqPort,ReqPort>
        ArtificialProvPortOldToNew : Map<ProvPort,ProvPort>
                

        //Maps from new path to old path (TODO: when not necessary, delete); or change to newToOrigin
        ArtificialFieldsNewToOld : Map<FieldPath,FieldPath> 
        ArtificialFaultsNewToOld : Map<FaultPath,FaultPath>        
        ArtificialReqPortNewToOld : Map<ReqPortPath,ReqPortPath>
        ArtificialProvPortNewToOld : Map<ProvPortPath,ProvPortPath>
        
        FaultsToRewrite : FaultDecl list    //declared in parent
        ProvPortsToRewrite : ProvPortDecl list    //declared in parent
        StepsToRewrite : StepDecl list    //declared in parent
        ArtificialStep : (ReqPort*ProvPort) option
    }
        with
            member levelUp.oldToNewMaps1 =                
                    (levelUp.ArtificialReqPortOldToNew,levelUp.ArtificialFaultsOldToNew,Map.empty<Var,Var>,levelUp.ArtificialFieldsOldToNew)
            member levelUp.oldToNewMaps2 =                
                    (levelUp.ArtificialFaultsOldToNew)
            member levelUp.oldToNewMaps3=                
                    (levelUp.ArtificialFaultsOldToNew,levelUp.ArtificialFieldsOldToNew)
            interface IScmMutable<'traceableOfOrigin,ScmRewriterLevelUpState<'traceableOfOrigin>> with
                member this.getTraceables =
                    let imodel = this.Model :> IModel<Traceable>
                    imodel.getTraceables
                member this.getModel : ScmModel = this.Model
                member this.setModel (model:ScmModel) =
                    { this with
                        ScmRewriterLevelUpState.Model = model
                    }
                member this.getUncommittedForwardTracerMap : Map<Traceable,Traceable> = this.UncommittedForwardTracerMap
                member this.setUncommittedForwardTracerMap (forwardTracerMap:Map<Traceable,Traceable>) =
                    { this with
                        ScmRewriterLevelUpState.UncommittedForwardTracerMap = forwardTracerMap;
                    }
                member this.getTraceablesOfOrigin : 'traceableOfOrigin list = this.TraceablesOfOrigin
                member this.setTraceablesOfOrigin (traceableOfOrigin:('traceableOfOrigin list)) = {this with TraceablesOfOrigin=traceableOfOrigin}
                member this.getForwardTracer : ('traceableOfOrigin -> Traceable) = this.ForwardTracer
                member this.setForwardTracer (forwardTracer:('traceableOfOrigin -> Traceable)) = {this with ForwardTracer=forwardTracer}
            interface IScmChangeSubcomponent<'traceableOfOrigin,ScmRewriterLevelUpState<'traceableOfOrigin>> with
                member this.getPathOfChangingSubcomponent = this.PathOfChangingSubcomponent
                member this.setPathOfChangingSubcomponent (compPath:CompPath) =
                    { this with
                        ScmRewriterLevelUpState.PathOfChangingSubcomponent = compPath
                    }
            interface IFreshNameDepot<ScmRewriterLevelUpState<'traceableOfOrigin>> with
                member this.getTakenNames : Set<string> = this.TakenNames
                member this.setTakenNames (takenNames:Set<string>) =
                    { this with
                        ScmRewriterLevelUpState.TakenNames = takenNames
                    }
    type ScmRewriterLevelUpFunction<'traceableOfOrigin,'returnType> =
        WorkflowFunction<ScmRewriterLevelUpState<'traceableOfOrigin>,ScmRewriterLevelUpState<'traceableOfOrigin>,'returnType>
    
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Accessor Functions to ScmRewriterLevelUp (and ScmRewriterState
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    
    let getParentCompDecl () : ScmRewriterLevelUpFunction<_,CompDecl> = 
        ScmRewriterBase.getSubComponentToChange ()
        
    let updateParentCompDecl (newParent:CompDecl) : ScmRewriterLevelUpFunction<_,unit> = 
        ScmRewriterBase.updateSubComponentToChange newParent

    let getChildPath () : ScmRewriterLevelUpFunction<_,CompPath>  = workflow {
        let! state = getState ()
        return (state.NameOfChildToRewrite.Value ::state.PathOfChangingSubcomponent)
    }

    let getChildCompDecl () : ScmRewriterLevelUpFunction<_,CompDecl>  = workflow {
        let! state = getState ()
        let! parent = getParentCompDecl ()
        let childName = state.NameOfChildToRewrite.Value
        let childCompDecl =
            parent.Subs |> List.find (fun subComp -> subComp.Comp = childName)
        return childCompDecl
    }
       
    let getLevelUpState () : ScmRewriterLevelUpFunction<_,ScmRewriterLevelUpState<'traceableOfOrigin>> =
        getState ()

    let updateLevelUpState (newLevelUp:ScmRewriterLevelUpState<'traceableOfOrigin>) : ScmRewriterLevelUpFunction<_,unit> = 
        updateState newLevelUp
            
    let addArtificialField (oldField:Field) (newField:Field) : ScmRewriterLevelUpFunction<_,unit> = workflow {
        let! state = getState ()
        let! levelUp = getLevelUpState ()
        let parentPath = state.PathOfChangingSubcomponent
        let childPath = levelUp.NameOfChildToRewrite.Value::parentPath
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUpState.ArtificialFieldsOldToNew = levelUp.ArtificialFieldsOldToNew.Add( oldField,newField );
                ScmRewriterLevelUpState.ArtificialFieldsNewToOld = levelUp.ArtificialFieldsNewToOld.Add( (parentPath,newField), (childPath,oldField) );
            }
        do! updateLevelUpState newLevelUp
    }

    let addArtificialFault (oldFault:Fault) (newFault:Fault) : ScmRewriterLevelUpFunction<_,unit> = workflow {
        let! state = getState ()
        let! levelUp = getLevelUpState ()
        let parentPath = state.PathOfChangingSubcomponent
        let childPath = levelUp.NameOfChildToRewrite.Value::parentPath
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUpState.ArtificialFaultsOldToNew = levelUp.ArtificialFaultsOldToNew.Add( oldFault,newFault );
                ScmRewriterLevelUpState.ArtificialFaultsNewToOld = levelUp.ArtificialFaultsNewToOld.Add( (parentPath,newFault), (childPath,oldFault) );
            }
        do! updateLevelUpState newLevelUp
    }

    let addArtificialReqPort (oldReqPort:ReqPort) (newReqPort:ReqPort) : ScmRewriterLevelUpFunction<_,unit> = workflow {
        let! state = getState ()
        let! levelUp = getLevelUpState ()
        let parentPath = state.PathOfChangingSubcomponent
        let childPath = levelUp.NameOfChildToRewrite.Value::parentPath
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUpState.ArtificialReqPortOldToNew = levelUp.ArtificialReqPortOldToNew.Add( oldReqPort,newReqPort );
                ScmRewriterLevelUpState.ArtificialReqPortNewToOld = levelUp.ArtificialReqPortNewToOld.Add( (parentPath,newReqPort), (childPath,oldReqPort) );
            }
        do! updateLevelUpState newLevelUp
    }

    let addArtificialProvPort (oldProvPort:ProvPort) (newProvPort:ProvPort) : ScmRewriterLevelUpFunction<_,unit> = workflow {
        let! state = getState ()
        let! levelUp = getLevelUpState ()
        let parentPath = state.PathOfChangingSubcomponent
        let childPath = levelUp.NameOfChildToRewrite.Value::parentPath
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUpState.ArtificialProvPortOldToNew = levelUp.ArtificialProvPortOldToNew.Add( oldProvPort,newProvPort );
                ScmRewriterLevelUpState.ArtificialProvPortNewToOld = levelUp.ArtificialProvPortNewToOld.Add( (parentPath,newProvPort), (childPath,oldProvPort) );
            }
        do! updateLevelUpState newLevelUp
    }
    
    let popFaultToRewrite () : ScmRewriterLevelUpFunction<_,FaultDecl option> = workflow {
        let! levelUp = getLevelUpState ()
        if levelUp.FaultsToRewrite.IsEmpty then
            return None
        else
            let faultToRewrite = levelUp.FaultsToRewrite.Head
            let newLevelUp = 
                { levelUp with
                    ScmRewriterLevelUpState.FaultsToRewrite = levelUp.FaultsToRewrite.Tail;
                }
            do! updateLevelUpState newLevelUp
            return Some(faultToRewrite)
    }
    
    let popProvPortToRewrite () : ScmRewriterLevelUpFunction<_,ProvPortDecl option> = workflow {
        let! levelUp = getLevelUpState ()
        if levelUp.ProvPortsToRewrite.IsEmpty then
            return None
        else
            let provPortToRewrite = levelUp.ProvPortsToRewrite.Head
            let newLevelUp = 
                { levelUp with
                    ScmRewriterLevelUpState.ProvPortsToRewrite = levelUp.ProvPortsToRewrite.Tail;
                }
            do! updateLevelUpState newLevelUp
            return Some(provPortToRewrite)
    }

    let popStepToRewrite () : ScmRewriterLevelUpFunction<_,StepDecl option> = workflow {
        let! levelUp = getLevelUpState ()
        if levelUp.StepsToRewrite.IsEmpty then
            return None
        else
            let stepToRewrite = levelUp.StepsToRewrite.Head
            let newLevelUp = 
                { levelUp with
                    ScmRewriterLevelUpState.StepsToRewrite = levelUp.StepsToRewrite.Tail;
                }
            do! updateLevelUpState newLevelUp
            return Some(stepToRewrite)
    }

    
    let pushFaultToRewrite (faultToRewrite:FaultDecl) : ScmRewriterLevelUpFunction<_,unit> = workflow {
        let! levelUp = getLevelUpState ()
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUpState.FaultsToRewrite = faultToRewrite::levelUp.FaultsToRewrite;
            }
        do! updateLevelUpState newLevelUp
        return ()
    }

    let pushProvPortToRewrite (provPortToRewrite:ProvPortDecl) : ScmRewriterLevelUpFunction<_,unit> = workflow {
        let! levelUp = getLevelUpState ()
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUpState.ProvPortsToRewrite = provPortToRewrite::levelUp.ProvPortsToRewrite;
            }
        do! updateLevelUpState newLevelUp
        return ()
    }
    
    let allParentStepsShouldBeRewrittenLater () : ScmRewriterLevelUpFunction<_,unit> = workflow {
        let! levelUp = getLevelUpState ()
        let! parentCompDecl = getParentCompDecl ()
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUpState.StepsToRewrite = parentCompDecl.Steps;
            }
        do! updateLevelUpState newLevelUp
        return ()
    }

    
    let setArtificialStep (reqport:ReqPort,provPort:ProvPort) : ScmRewriterLevelUpFunction<_,unit> = workflow {
        let! levelUp = getLevelUpState ()
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUpState.ArtificialStep = Some(reqport,provPort);
            }
        do! updateLevelUpState newLevelUp
        return ()
    }

    let getArtificialStep () : ScmRewriterLevelUpFunction<_,ReqPort*ProvPort> = workflow {
        let! levelUp = getLevelUpState ()
        return levelUp.ArtificialStep.Value
    }

    
    (*


    let push (oldProvPort:ProvPort) (newProvPort:ProvPort) : ScmRewriterLevelUpFunction<unit,_> = workflow {
        let! levelUp = getLevelUpState
        let newLevelUp = 
            { levelUp with
                ScmRewriterLevelUpState.ArtificialProvPortOldToNew = levelUp.ArtificialProvPortOldToNew.Add( oldProvPort,newProvPort );
                ScmRewriterLevelUpState.ArtificialProvPortNewToOld = levelUp.ArtificialProvPortNewToOld.Add( (parentPath,newProvPort), (childPath,oldProvPort) );
            }
        do! updateLevelUpState newLevelUp
    }

    *)

    
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Leveling up
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    let levelUpField () : ScmRewriterLevelUpFunction<_,unit> = workflow {
        // parent is target, child is source
        let! childCompDecl = getChildCompDecl ()
        let! childPath = getChildPath ()
        let! parentCompDecl = getParentCompDecl ()
        let! parentPath = getPathOfSubComponentToChange ()

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
            do! iscmTraceTraceable (Traceable.TraceableField(childPath,field)) (Traceable.TraceableField(parentPath,transformedField))
        }

    let levelUpFault () : ScmRewriterLevelUpFunction<_,unit> = workflow {
        // parent is target, child is source
        let! childCompDecl = getChildCompDecl ()
        let! childPath = getChildPath ()
        let! parentCompDecl = getParentCompDecl ()
        let! parentPath = getPathOfSubComponentToChange ()
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
            do! iscmTraceTraceable (Traceable.TraceableFault(childPath,fault)) (Traceable.TraceableFault(parentPath,transformedFault))
        }
    let levelUpReqPort () : ScmRewriterLevelUpFunction<_,unit> = workflow {
        // parent is target, child is source
        let! childCompDecl = getChildCompDecl ()
        let! parentCompDecl = getParentCompDecl ()

        if childCompDecl.ReqPorts.IsEmpty then
            // do not modify old tainted state here
            return ()
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
    let levelUpProvPort () : ScmRewriterLevelUpFunction<_,unit> = workflow {            
        let! levelUp = getLevelUpState ()
        
        let getUnusedProvPortNameIfNotInMap (oldProv:ProvPort) (basedOn:string) : ScmRewriterLevelUpFunction<_,ProvPort> = workflow {
            let! levelUp = getLevelUpState ()
            if levelUp.ArtificialProvPortOldToNew.ContainsKey oldProv then
                return (levelUp.ArtificialProvPortOldToNew.Item oldProv)
            else
                let! newProvPortName = getUnusedProvPortName basedOn
                return newProvPortName
        }
            
        // parent is target, child is source
        let! childCompDecl = getChildCompDecl ()
        let! parentCompDecl = getParentCompDecl ()

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
       
    let levelUpAndRewriteBindingDeclaredInChild () : ScmRewriterLevelUpFunction<_,unit> = workflow {
        // Cases: (view from parent, where sub1 is selected)                    
        //   Declared in ancestor (done in rule rewriteBindingsDeclaredInAncestors)
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
        let! levelUp = getLevelUpState ()
        // parent is target, child is source
        let! childCompDecl = getChildCompDecl ()
        let! parentCompDecl = getParentCompDecl ()

        if childCompDecl.Bindings.IsEmpty then
            // do not modify old tainted state here
            return ()
        else
            let bindingDecl = childCompDecl.Bindings.Head
            
            // printfn ""
            // printfn "%s: %s-%s -> %s-%s" childCompDecl.getName (bindingDecl.Source.Comp |> List.map (fun c -> c.getName) |> String.concat ".") (bindingDecl.Source.ProvPort.getName) (bindingDecl.Target.Comp  |> List.map (fun c -> c.getName) |> String.concat ".") (bindingDecl.Target.ReqPort.getName)

            assert (bindingDecl.Source.Comp = [childCompDecl.Comp]) //because the subcomponent has itself no subcomponent (we chose it so), it cannot have a binding from a subcomponent
            assert (bindingDecl.Target.Comp = [childCompDecl.Comp]) //because the subcomponent has itself no subcomponent (we chose it so), it cannot have a binding to a subcomponent
            let newChildCompDecl = childCompDecl.removeBinding bindingDecl
            let newTarget =
                let newReqPort = levelUp.ArtificialReqPortOldToNew.Item (bindingDecl.Target.ReqPort)
                {
                    BndTarget.Comp = [parentCompDecl.Comp];
                    BndTarget.ReqPort = newReqPort;
                }
            let newSource =
                let newProvPort = levelUp.ArtificialProvPortOldToNew.Item (bindingDecl.Source.ProvPort)
                {
                    BndSrc.Comp = [parentCompDecl.Comp];
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
        
    let rewriteBindingsDeclaredInAncestors () : ScmRewriterLevelUpFunction<_,unit> = workflow {
        // Cases: (view from parent, where sub1 is selected)                    
        //   Declared in ancestor (done here)
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

        // This function is the only function in LevelUp, which has to look and rewrite every ancestor of the component which gets upleveled.
        // Luckily it is enough to look at every ancestor* and not every component in the whole model.
        let! model = iscmGetModel ()
        let rootComp = match model with | ScmModel(rootComp) -> rootComp
        let! levelUp = getLevelUpState ()
              
        let rewriteBinding (relativeLeveledUpPath:CompPath) (bindingToRewrite:BndDecl) : BndDecl =
            let relChildPathToCheckFor = relativeLeveledUpPath
            let relParentPath = relativeLeveledUpPath.Tail
            let newSource =
                let oldCompPathInBinding = bindingToRewrite.Source.Comp
                if oldCompPathInBinding = [] then
                    failwith "path in binding should at least contain the name of the component itself"
                else if relChildPathToCheckFor = oldCompPathInBinding then
                    let port = levelUp.ArtificialProvPortOldToNew.Item (bindingToRewrite.Source.ProvPort)
                    {
                        BndSrc.Comp = relParentPath ; //new port is in parent
                        BndSrc.ProvPort = port
                    }
                else
                    bindingToRewrite.Source
            let newTarget =
                let oldCompPathInBinding = bindingToRewrite.Target.Comp
                if oldCompPathInBinding = [] then
                    failwith "path in binding should at least contain the name of the component itself"
                else if relChildPathToCheckFor = oldCompPathInBinding then
                    let port = levelUp.ArtificialReqPortOldToNew.Item (bindingToRewrite.Target.ReqPort)
                    {
                        BndTarget.Comp = relParentPath ; //new port is in parent
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
            transformedBinding

        let compRewriter (relativeLeveledUpPath:CompPath) (currentComp:CompDecl) : CompDecl =
            { currentComp with
                CompDecl.Bindings = currentComp.Bindings |> List.map (rewriteBinding (relativeLeveledUpPath:CompPath))
            }
                            
        let! childCompDecl = getChildCompDecl ()
        let! fullPathToChild = getChildPath ()
        let fullPathToParent = fullPathToChild.Tail
        let relativePathToChild = [fullPathToChild.Head] //viewport of parent

        let newRootComp = rootComp.rewriteAncestors compRewriter fullPathToParent relativePathToChild childCompDecl
        do! iscmSetModel (ScmModel(newRootComp))
    }

    

    
    let rewriteContractsDeclaredInAncestors () : ScmRewriterLevelUpFunction<_,unit> = workflow {
        // fields and faults need to be upleveled first
        let! model = iscmGetModel ()
        let rootComp = match model with | ScmModel(rootComp) -> rootComp
        let! levelUp = getLevelUpState ()

        let rewriteContract (relativeLeveledUpPath:CompPath) (contractToRewrite:Contract) : Contract =            
            let relChildPathToCheckFor = relativeLeveledUpPath
            let relParentPath = relativeLeveledUpPath.Tail
            contractToRewrite.rewriteLocation relChildPathToCheckFor relParentPath levelUp.oldToNewMaps3
        
        let rewriteContractOfStep (relativeLeveledUpPath:CompPath) (stepToRewrite:StepDecl) : StepDecl =
            { stepToRewrite with
                StepDecl.Contract = rewriteContract relativeLeveledUpPath stepToRewrite.Contract 
            }
        let rewriteContractOfProvPort (relativeLeveledUpPath:CompPath) (provPortToRewrite:ProvPortDecl) : ProvPortDecl =
            { provPortToRewrite with
                ProvPortDecl.Contract = rewriteContract relativeLeveledUpPath provPortToRewrite.Contract 
            }        
        let compRewriter (relativeLeveledUpPath:CompPath) (currentComp:CompDecl) : CompDecl =
            { currentComp with
                CompDecl.ProvPorts = currentComp.ProvPorts |> List.map (rewriteContractOfProvPort (relativeLeveledUpPath))
                CompDecl.Steps     = currentComp.Steps     |> List.map (rewriteContractOfStep     (relativeLeveledUpPath))
            }                            
                
        let! childCompDecl = getChildCompDecl ()
        let! fullPathToChild = getChildPath ()
        let fullPathToParent = fullPathToChild.Tail
        let relativePathToChild = [fullPathToChild.Head] //viewport of parent

        let newRootComp = rootComp.rewriteAncestors compRewriter fullPathToParent relativePathToChild childCompDecl
        do! iscmSetModel (ScmModel(newRootComp))

    }

        
    let createArtificialStep () : ScmRewriterLevelUpFunction<_,unit> = workflow {
        let! levelUp = getLevelUpState ()
        // parent is target, child is source
        let! childCompDecl = getChildCompDecl ()
        let! parentCompDecl = getParentCompDecl ()


        if childCompDecl.Steps.IsEmpty then
            // do not modify old tainted state here
            return ()
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
                        BndDecl.Target = {BndTarget.Comp = [childCompDecl.Comp]; BndTarget.ReqPort = reqPort};
                        BndDecl.Source = {BndSrc.Comp = [childCompDecl.Comp]; BndSrc.ProvPort = provPort};
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


    let convertStepToPort () : ScmRewriterLevelUpFunction<_,unit> = workflow {
        do! createArtificialStep ()
            
    // replace step to required port and provided port and binding, add a link from subcomponent path to new required port
        // parent is target, child is source
        let! childCompDecl = getChildCompDecl ()
        let! parentCompDecl = getParentCompDecl ()
        if childCompDecl.Steps.IsEmpty then
            // do not modify old tainted state here
            return ()
        else
            let! (reqPort,provPort) = getArtificialStep ()

            let stepToConvert = childCompDecl.Steps.Head
            let newProvPortDecl =
                {
                    ProvPortDecl.FaultExpr = stepToConvert.FaultExpr;
                    ProvPortDecl.ProvPort = provPort;
                    ProvPortDecl.Params = [];
                    ProvPortDecl.Behavior = stepToConvert.Behavior;
                    ProvPortDecl.Contract = stepToConvert.Contract
                }
            let newChildCompDecl = childCompDecl.removeStep(stepToConvert)
                                                        .addProvPort(newProvPortDecl)
            let newParentCompDecl = parentCompDecl.replaceChild(childCompDecl,newChildCompDecl)
                    
            do! updateParentCompDecl newParentCompDecl
            do! allParentStepsShouldBeRewrittenLater () // all parent steps need to be rewritten later. The step comp must be replaced by the new reqport-call
            do! pushProvPortToRewrite newProvPortDecl
        }

    let rewriteParentStep () : ScmRewriterLevelUpFunction<_,unit> = workflow {
        // here, additionally instead of "step subcomponent" the converted step must be called
        let! levelUp = getLevelUpState ()
        if levelUp.ArtificialStep.IsNone then
            return ()
        else
            let! parentCompDecl = getParentCompDecl ()
            let! childPath = getChildPath ()
            let! stepToRewrite = popStepToRewrite ()
                                
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
                                    if comp = childPath.Head then //do we actually replace the step of the child?
                                        Stm.CallPort (stepReqPortNowInParent,[])
                                    else
                                        stm
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

    let rewriteProvPort () : ScmRewriterLevelUpFunction<_,unit> = workflow {
        // replace reqPorts and fields by their proper names, replace Fault Expressions, adapt Contracts
            
        let! levelUp = getLevelUpState ()
        let! parentCompDecl = getParentCompDecl ()
        let! childCompDecl = getChildCompDecl ()
                                
        let! provPortToRewrite = popProvPortToRewrite ()
        match provPortToRewrite with
            | None ->
                // do not modify old tainted state here
                return ()
            | Some(provPortToRewrite) ->
                // we are in a parent Component!!!
                let oldLoc = [childCompDecl.Comp]
                let newLoc = [parentCompDecl.Comp]
                let rewrittenProvPort =
                    {
                        ProvPortDecl.FaultExpr = rewriteFaultExprOption levelUp.oldToNewMaps2 provPortToRewrite.FaultExpr;
                        ProvPortDecl.ProvPort = provPortToRewrite.ProvPort;
                        ProvPortDecl.Params = provPortToRewrite.Params; // The getUnusedxxxName-Functions also ensured, that the names of new fields and faults,... do not overlap with any param. So we can keep it
                        ProvPortDecl.Behavior = rewriteBehavior levelUp.oldToNewMaps1 provPortToRewrite.Behavior;
                        ProvPortDecl.Contract = provPortToRewrite.Contract.rewriteLocation oldLoc newLoc levelUp.oldToNewMaps3
                    }
                let newParentCompDecl = parentCompDecl.replaceProvPort(provPortToRewrite,rewrittenProvPort)
                do! updateParentCompDecl newParentCompDecl                        
        }

    let rewriteFaults () : ScmRewriterLevelUpFunction<_,unit> = workflow {
        // replace reqPorts and fields by their proper names, replace Fault Expressions
        let! levelUp = getLevelUpState ()
        let! parentCompDecl = getParentCompDecl ()
                
        let! faultToRewrite = popFaultToRewrite ()
        match faultToRewrite with
            | None ->
                // do not modify old tainted state here
                return ()
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
    let assertSubcomponentEmpty () : ScmRewriterLevelUpFunction<_,unit> = workflow {
            let! childCompDecl = getChildCompDecl ()

            assert (childCompDecl.Subs = [])
            assert (childCompDecl.Fields = [])
            assert (childCompDecl.Faults = [])
            assert (childCompDecl.ReqPorts = [])
            assert (childCompDecl.ProvPorts = [])
            assert (childCompDecl.Bindings = [])
            return ()
        }
    let removeSubComponent () : ScmRewriterLevelUpFunction<_,unit> = workflow {            
            let! parentCompDecl = getParentCompDecl ()
            let! childCompDecl = getChildCompDecl ()
            let newParentCompDecl = parentCompDecl.removeChild(childCompDecl)
            do! updateParentCompDecl newParentCompDecl
        }        

                
    let levelUpSubcomponent () : ScmRewriterLevelUpFunction<_,unit> = workflow {
        // idea:
        //  1. convert: Convert step in subcomponent to a port
        //  2. levelUp: LevelUp every element of the subcomponent. New names are created. Create a map to be able track from the old name to the new name of an element
        //  3. rewrite parent steps: "step subcomponent" is rewritten to PortCall (of step 1, which got upleveled in step 2)
        //  4. rewrite upleveled: Rewrite every _upleveled_ Element. Adapt: Change the names of the old identifiers to the names of the new identifiers using the map of step 2.
        //  5. rewrite ancestors: Sometimes elements in an ancestor use a path, which refer to elements in the upleveled subcomponent. These path must be updated to the elements in the parent component.
        do! (iterateToFixpoint (convertStepToPort ()))
        do! (iterateToFixpoint (levelUpField ())) //Invariant: Imagine LevelUp are written back into model. Fieldaccess (read/write) is either on the "real" field or on a "forwarded field" (map entry in ArtificialFieldsOldToNew exists, and new field exists)
        do! (iterateToFixpoint (levelUpFault ()))
        do! (iterateToFixpoint (levelUpReqPort ()))
        do! (iterateToFixpoint (levelUpProvPort ()))
        do! (iterateToFixpoint (levelUpAndRewriteBindingDeclaredInChild ()))
        do! (iterateToFixpoint (rewriteParentStep ()))
        do! (iterateToFixpoint (rewriteProvPort ()))
        do! (iterateToFixpoint (rewriteFaults ()))
        do! (rewriteBindingsDeclaredInAncestors ())
        do! (rewriteContractsDeclaredInAncestors ())
        do! assertSubcomponentEmpty ()
        // do! assertSubcomponentNotReferenced
        do! removeSubComponent ()
    }
              
    let findSubComponentForLevelingUp () : IScmMutableWorkflowFunction<_,_,CompPath option> = workflow {
        let! model = ScmMutable.iscmGetModel ()
        let rootComp = match model with | ScmModel(rootComp) -> rootComp
        if rootComp.Subs = [] then
            // nothing to do, we are done
            return None
        else
            // find component with no subcomponent, which is not the root. there must exist at least one
            let rec findLeaf (parentPath:CompPath) (node:CompDecl) : CompPath =
                let nodePath = node.Comp::parentPath
                if node.Subs=[] then
                    nodePath
                else
                    let firstChild = node.Subs.Head
                    findLeaf nodePath firstChild
            let leaf = findLeaf ([]) (rootComp)
            return Some(leaf)
    }

    let createLevelUpStateForSubComponent
            (model:ScmModel)
            (uncommittedForwardTracerMap:Map<Traceable,Traceable>)
            (traceablesOfOrigin : 'traceableOfOrigin list)
            (forwardTracer : 'traceableOfOrigin -> Traceable)
            (subComponentToLevelUp:CompPath) =
        let rootComp = match model with | ScmModel(rootComp) -> rootComp
        let parentPath = subComponentToLevelUp.Tail
        let parentCompDecl = rootComp.getDescendantUsingPath parentPath
        let childName = subComponentToLevelUp.Head
        let newLevelUp =
            {
                ScmRewriterLevelUpState.Model = model;
                ScmRewriterLevelUpState.UncommittedForwardTracerMap = uncommittedForwardTracerMap;
                ScmRewriterLevelUpState.TraceablesOfOrigin = traceablesOfOrigin;
                ScmRewriterLevelUpState.ForwardTracer = forwardTracer;
                ScmRewriterLevelUpState.PathOfChangingSubcomponent = parentPath;
                ScmRewriterLevelUpState.TakenNames = rootComp.getTakenNames () |> Set.ofList;
                ScmRewriterLevelUpState.NameOfChildToRewrite = Some(childName);
                ScmRewriterLevelUpState.ArtificialFieldsOldToNew = Map.empty<Field,Field>;
                ScmRewriterLevelUpState.ArtificialFaultsOldToNew = Map.empty<Fault,Fault>;
                ScmRewriterLevelUpState.ArtificialReqPortOldToNew = Map.empty<ReqPort,ReqPort>;
                ScmRewriterLevelUpState.ArtificialProvPortOldToNew = Map.empty<ProvPort,ProvPort>;
                ScmRewriterLevelUpState.ArtificialFieldsNewToOld = Map.empty<FieldPath,FieldPath>;
                ScmRewriterLevelUpState.ArtificialFaultsNewToOld = Map.empty<FaultPath,FaultPath>;
                ScmRewriterLevelUpState.ArtificialReqPortNewToOld = Map.empty<ReqPortPath,ReqPortPath>;
                ScmRewriterLevelUpState.ArtificialProvPortNewToOld = Map.empty<ProvPortPath,ProvPortPath>;
                ScmRewriterLevelUpState.FaultsToRewrite = [];
                ScmRewriterLevelUpState.ProvPortsToRewrite = [];
                ScmRewriterLevelUpState.StepsToRewrite = [];
                ScmRewriterLevelUpState.ArtificialStep = None;
            }
        newLevelUp
        
        
    let selectAndLevelUpSubcomponent () = workflow {
        let! subComponentToLevelUp = findSubComponentForLevelingUp ()
        let! uncommittedForwardTracerMap = iscmGetUncommittedForwardTracerMap ()
        let! traceablesOfOrigin = iscmGetTraceablesOfOrigin ()
        let! forwardTracer = iscmGetForwardTracer ()
        match subComponentToLevelUp with
            | None -> return ()
            | Some(subComponentToLevelUp) ->
                let! state = getState ()
                do! updateState (createLevelUpStateForSubComponent state.Model uncommittedForwardTracerMap traceablesOfOrigin forwardTracer subComponentToLevelUp)
                do! levelUpSubcomponent ()
    }
    
    let selectSpecificSubcomponent (subComponentToLevelUp:CompPath) = workflow {
        let! state = getState ()
        let! uncommittedForwardTracerMap = iscmGetUncommittedForwardTracerMap ()
        do! updateState (createLevelUpStateForSubComponent state.Model uncommittedForwardTracerMap subComponentToLevelUp)
    }
    
    
    let assertNoSubcomponent () : IScmMutableWorkflowFunction<_,_,unit> = workflow {
        let! model = ScmMutable.iscmGetModel ()
        let rootComp = match model with | ScmModel(rootComp) -> rootComp
        assert (rootComp.Subs=[])
        return ()
    }
    
    let prepareForLevelingUp<'traceableOfOrigin,'oldState when 'oldState :> IScmMutable<'traceableOfOrigin,'oldState>> ()
                        : ExogenousWorkflowFunction<'oldState,ScmRewriterLevelUpState<'traceableOfOrigin>> = workflow {
        let emptyLevelUpState
                (model:ScmModel)
                (uncommittedForwardTracerMap:Map<Traceable,Traceable>)
                (traceablesOfOrigin : 'traceableOfOrigin list)
                (forwardTracer : 'traceableOfOrigin -> Traceable) = 
            let rootComp = match model with | ScmModel(rootComp) -> rootComp
            {
                ScmRewriterLevelUpState.Model = model;
                ScmRewriterLevelUpState.UncommittedForwardTracerMap = uncommittedForwardTracerMap;
                ScmRewriterLevelUpState.TraceablesOfOrigin = traceablesOfOrigin;
                ScmRewriterLevelUpState.ForwardTracer = forwardTracer;
                ScmRewriterLevelUpState.PathOfChangingSubcomponent = [rootComp.Comp];
                ScmRewriterLevelUpState.TakenNames = Set.empty<string>
                ScmRewriterLevelUpState.NameOfChildToRewrite = None;
                ScmRewriterLevelUpState.ArtificialFieldsOldToNew = Map.empty<Field,Field>;
                ScmRewriterLevelUpState.ArtificialFaultsOldToNew = Map.empty<Fault,Fault>;
                ScmRewriterLevelUpState.ArtificialReqPortOldToNew = Map.empty<ReqPort,ReqPort>;
                ScmRewriterLevelUpState.ArtificialProvPortOldToNew = Map.empty<ProvPort,ProvPort>;
                ScmRewriterLevelUpState.ArtificialFieldsNewToOld = Map.empty<FieldPath,FieldPath>;
                ScmRewriterLevelUpState.ArtificialFaultsNewToOld = Map.empty<FaultPath,FaultPath>;
                ScmRewriterLevelUpState.ArtificialReqPortNewToOld = Map.empty<ReqPortPath,ReqPortPath>;
                ScmRewriterLevelUpState.ArtificialProvPortNewToOld = Map.empty<ProvPortPath,ProvPortPath>;
                ScmRewriterLevelUpState.FaultsToRewrite = [];
                ScmRewriterLevelUpState.ProvPortsToRewrite = [];
                ScmRewriterLevelUpState.StepsToRewrite = [];
                ScmRewriterLevelUpState.ArtificialStep = None;
            }
        let! model = iscmGetModel ()
        let! uncommittedForwardTracerMap = iscmGetUncommittedForwardTracerMap ()
        let! traceablesOfOrigin = iscmGetTraceablesOfOrigin ()
        let! forwardTracer = iscmGetForwardTracer ()
        do! updateState (emptyLevelUpState model uncommittedForwardTracerMap traceablesOfOrigin forwardTracer)
    }


    // This function must implement the conversion from 'oldState to ScmRewriterLevelUpState
    let levelUpSubcomponentsWrapper<'traceableOfOrigin,'oldState when 'oldState :> IScmMutable<'traceableOfOrigin,'oldState>> ()
                        : ExogenousWorkflowFunction<'oldState,ScmRewriterLevelUpState<'traceableOfOrigin>> = workflow {
        do! prepareForLevelingUp ()
        do! (iterateToFixpoint (selectAndLevelUpSubcomponent ()))
        do! assertNoSubcomponent ()
    }

    
    let initialLevelUpState (scm:ScmModel) (subComponentToLevelUp:CompPath) =
        createLevelUpStateForSubComponent scm (Map.empty<Traceable,Traceable>) subComponentToLevelUp 