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

module internal ScmRewriter =
    open ScmHelpers

    type ScmModel = CompDecl //may change, but I hope it does not
    
    type ScmRewriterCurrentSelection = {
        ChildPath : CompPath;
        ParentPath : CompPath;
        ChildCompDecl : CompDecl;
        ParentCompDecl : CompDecl;
        // Forwarder
        ArtificialFieldsOldToNew : Map<FieldPath,FieldPath> //Map from old path to new path (TODO: when not necessary, delete)
        ArtificialFieldsNewToOld : Map<FieldPath,FieldPath> //Map from new path to old path (TODO: when not necessary, delete)
        
        ArtificialReqPortOldToNew : Map<ReqPortPath,ReqPortPath> //Map from old path to new path (TODO: when not necessary, delete)
        ArtificialReqPortNewToOld : Map<ReqPortPath,ReqPortPath> //Map from new path to old path (TODO: when not necessary, delete)

        ArtificialProvPortOldToNew : Map<ProvPortPath,ProvPortPath> //Map from old path to new path (TODO: when not necessary, delete)
        ArtificialProvPortNewToOld : Map<ProvPortPath,ProvPortPath> //Map from new path to old path (TODO: when not necessary, delete)
    }
        with
            static member createEmptyFromPath (model:CompDecl) (path:CompPath) =
                {
                    ScmRewriterCurrentSelection.ChildPath = path;
                    ScmRewriterCurrentSelection.ParentPath = path.Tail;
                    ScmRewriterCurrentSelection.ChildCompDecl = model.getDescendantUsingPath path;
                    ScmRewriterCurrentSelection.ParentCompDecl = model.getDescendantUsingPath path.Tail;
                    ScmRewriterCurrentSelection.ArtificialFieldsOldToNew = Map.empty<FieldPath,FieldPath>;
                    ScmRewriterCurrentSelection.ArtificialFieldsNewToOld = Map.empty<FieldPath,FieldPath>;
                    ScmRewriterCurrentSelection.ArtificialReqPortOldToNew = Map.empty<ReqPortPath,ReqPortPath>;
                    ScmRewriterCurrentSelection.ArtificialReqPortNewToOld = Map.empty<ReqPortPath,ReqPortPath>;
                    ScmRewriterCurrentSelection.ArtificialProvPortOldToNew = Map.empty<ProvPortPath,ProvPortPath>;
                    ScmRewriterCurrentSelection.ArtificialProvPortNewToOld = Map.empty<ProvPortPath,ProvPortPath>;
                }


    type ScmRewriteState = {
        Model : ScmModel;
        ChangedSubcomponents : ScmRewriterCurrentSelection option;
        // TODO: Optimization: Add parent of ComponentToRemove here. Thus, when a change to the componentToRemove is done, only its parent needs to be updated and not the whole model.
        //       The writeBack to the model can happen, when a component gets deleted
        // Flag, which determines, if something was changed (needed for fixpoint iteration)
        Tainted : bool;
    }
        with
            static member initial (scm:ScmModel) = 
                {
                    ScmRewriteState.Model = scm;
                    ScmRewriteState.ChangedSubcomponents = None;
                    ScmRewriteState.Tainted = false;
                }
                
    type ScmRewriteFunction<'a> = ScmRewriteFunction of (ScmRewriteState -> 'a * ScmRewriteState)
    
    // TODO:
    //   - RewriteElement should return, if it made a change
    //   - smallest element only gets called once
    //   - liftToFixpoint repeats a small element, until it doesn't change something anymore
    //   - so levelUpField levels up one field, levelUpFields levels up fields, until nothing possible anymore


    let runState (ScmRewriteFunction s) a = s a
    let getState = ScmRewriteFunction (fun s -> (s,s)) //Called in workflow: (implicitly) gets state (s) from workflow; assign this State s to the let!; and set (in this case keep)State of workflow to s
    let putState s = ScmRewriteFunction (fun _ -> ((),s)) //Called in workflow: ignore state (_) from workflow; assign nothing () to the let!; and set (in this case keep)State of workflow to the new state s

    // the computational expression "scmRewrite" is defined here
    type ScmRewriter() =
        member this.Return(a) = 
            ScmRewriteFunction (fun s -> (a,s))
        member this.Bind(m,k) =
            ScmRewriteFunction (fun state -> 
                let (a,state') = runState m state 
                runState (k a) state')
        member this.ReturnFrom (m) =
            m

    let scmRewrite = new ScmRewriter()
    let scmRewriteFixpoint = new ScmRewriter() //new ScmRewriteFixpoint. (fixpoint Computation Expression. Repeat something, until fixpoint is reached)


    // here the partial rewrite rules        
    let selectSubComponent : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            if (state.ChangedSubcomponents.IsSome) then
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
                    let selectedComponent = ScmRewriterCurrentSelection.createEmptyFromPath state.Model leaf
                    let modifiedState =
                        { state with
                            ScmRewriteState.ChangedSubcomponents = Some(selectedComponent);       
                        }
                    return! putState modifiedState
        }

    let levelUpField : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            if (state.ChangedSubcomponents.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.ChangedSubcomponents.Value
                // parent is target, child is source
                if infos.ChildCompDecl.Fields.IsEmpty then
                    // do not modify old tainted state here
                    return! putState state
                else
                    let fieldDecl = infos.ChildCompDecl.Fields.Head
                    let field = fieldDecl.Field
                    let newChildCompDecl = infos.ChildCompDecl.removeField field
                    let transformedField = infos.ParentCompDecl.getUnusedFieldName (sprintf "%s_%s" infos.ChildCompDecl.getName field.getName)
                    let transformedFieldDecl = 
                        {fieldDecl with
                            FieldDecl.Field = transformedField;
                        }                    
                    let newParentCompDecl = infos.ParentCompDecl.replaceChild(infos.ChildCompDecl,newChildCompDecl)
                                                                .addField(transformedFieldDecl)
                    let newChangedSubcomponents =
                        { infos with
                            ScmRewriterCurrentSelection.ChildCompDecl = newChildCompDecl;
                            ScmRewriterCurrentSelection.ParentCompDecl = newParentCompDecl;
                            ScmRewriterCurrentSelection.ArtificialFieldsOldToNew = infos.ArtificialFieldsOldToNew.Add( (infos.ChildPath,field), (infos.ParentPath,transformedField) );
                            ScmRewriterCurrentSelection.ArtificialFieldsNewToOld = infos.ArtificialFieldsNewToOld.Add( (infos.ParentPath,transformedField), (infos.ChildPath,field) );
                        }
                    let modifiedState =
                        { state with
                            ScmRewriteState.ChangedSubcomponents = Some(newChangedSubcomponents);
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
        }
    let levelUpFault : ScmRewriteFunction<unit> = scmRewrite {
            // TODO: No example and no test, yet
            (*
            let! state = getState
            if (state.ChangedSubcomponents.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.ChangedSubcomponents.Value
                // parent is target, child is source
                if infos.ChildCompDecl.Faults.IsEmpty then
                    // do not modify old tainted state here
                    return! putState state
                else
                    let reqPortDecl = infos.ChildCompDecl.ReqPorts.Head
                    let reqPort = reqPortDecl.ReqPort
                    let newChildCompDecl = infos.ChildCompDecl.removeReqPort reqPort
                    let transformedReqPort = infos.ParentCompDecl.getUnusedReqPortName (sprintf "%s_%s" infos.ChildCompDecl.getName reqPort.getName)
                    let transformedReqPortDecl = 
                        {reqPortDecl with
                            FaultDecl. = transformedReqPort;
                        }                    
                    let newParentCompDecl = infos.ParentCompDecl.replaceChild(infos.ChildCompDecl,newChildCompDecl)
                                                                .addReqPort(transformedReqPortDecl)
                    let newChangedSubcomponents =
                        { infos with
                            ScmRewriterCurrentSelection.ChildCompDecl = newChildCompDecl;
                            ScmRewriterCurrentSelection.ParentCompDecl = newParentCompDecl;
                            ScmRewriterCurrentSelection.ArtificialReqPortOldToNew = infos.ArtificialReqPortOldToNew.Add( (infos.ChildPath,reqPort), (infos.ParentPath,transformedReqPort) );
                            ScmRewriterCurrentSelection.ArtificialReqPortNewToOld = infos.ArtificialReqPortNewToOld.Add( (infos.ParentPath,transformedReqPort), (infos.ChildPath,reqPort) );
                        }
                    let modifiedState =
                        { state with
                            ScmRewriteState.ChangedSubcomponents = Some(newChangedSubcomponents);
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
                *)
                return ()
        }
    let levelUpReqPort : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            if (state.ChangedSubcomponents.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.ChangedSubcomponents.Value
                // parent is target, child is source
                if infos.ChildCompDecl.ReqPorts.IsEmpty then
                    // do not modify old tainted state here
                    return! putState state
                else
                    let reqPortDecl = infos.ChildCompDecl.ReqPorts.Head
                    let reqPort = reqPortDecl.ReqPort
                    let newChildCompDecl = infos.ChildCompDecl.removeReqPort reqPort
                    let transformedReqPort = infos.ParentCompDecl.getUnusedReqPortName (sprintf "%s_%s" infos.ChildCompDecl.getName reqPort.getName)
                    let transformedReqPortDecl = 
                        {reqPortDecl with
                            ReqPortDecl.ReqPort = transformedReqPort;
                        }                    
                    let newParentCompDecl = infos.ParentCompDecl.replaceChild(infos.ChildCompDecl,newChildCompDecl)
                                                                .addReqPort(transformedReqPortDecl)
                    let newChangedSubcomponents =
                        { infos with
                            ScmRewriterCurrentSelection.ChildCompDecl = newChildCompDecl;
                            ScmRewriterCurrentSelection.ParentCompDecl = newParentCompDecl;
                            ScmRewriterCurrentSelection.ArtificialReqPortOldToNew = infos.ArtificialReqPortOldToNew.Add( (infos.ChildPath,reqPort), (infos.ParentPath,transformedReqPort) );
                            ScmRewriterCurrentSelection.ArtificialReqPortNewToOld = infos.ArtificialReqPortNewToOld.Add( (infos.ParentPath,transformedReqPort), (infos.ChildPath,reqPort) );
                        }
                    let modifiedState =
                        { state with
                            ScmRewriteState.ChangedSubcomponents = Some(newChangedSubcomponents);
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
        }
    let levelUpProvPort : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            if (state.ChangedSubcomponents.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let infos = state.ChangedSubcomponents.Value
                // parent is target, child is source
                if infos.ChildCompDecl.ProvPorts.IsEmpty then
                    // do not modify old tainted state here
                    return! putState state
                else
                    let provPortDecl = infos.ChildCompDecl.ProvPorts.Head
                    let provPort = provPortDecl.ProvPort
                    let newChildCompDecl = infos.ChildCompDecl.removeProvPort provPort
                    let transformedProvPort = infos.ParentCompDecl.getUnusedProvPortName (sprintf "%s_%s" infos.ChildCompDecl.getName provPort.getName)
                    let transformedProvPortDecl = 
                        {provPortDecl with
                            ProvPortDecl.ProvPort = transformedProvPort;
                        }                    
                    let newParentCompDecl = infos.ParentCompDecl.replaceChild(infos.ChildCompDecl,newChildCompDecl)
                                                                .addProvPort(transformedProvPortDecl)
                    let newChangedSubcomponents =
                        { infos with
                            ScmRewriterCurrentSelection.ChildCompDecl = newChildCompDecl;
                            ScmRewriterCurrentSelection.ParentCompDecl = newParentCompDecl;
                            ScmRewriterCurrentSelection.ArtificialProvPortOldToNew = infos.ArtificialProvPortOldToNew.Add( (infos.ChildPath,provPort), (infos.ParentPath,transformedProvPort) );
                            ScmRewriterCurrentSelection.ArtificialProvPortNewToOld = infos.ArtificialProvPortNewToOld.Add( (infos.ParentPath,transformedProvPort), (infos.ChildPath,provPort) );
                        }
                    let modifiedState =
                        { state with
                            ScmRewriteState.ChangedSubcomponents = Some(newChangedSubcomponents);
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
        }
    let levelUpAndRewriteBinding : ScmRewriteFunction<unit> = scmRewrite {
            return ()
        }
    let convertStepToPort : ScmRewriteFunction<unit> = scmRewrite {
            // replace step to required port and provided port and binding, add a link from subcomponent path to new required port
            // TODO: rewrite names in faultExpression?!?
            return ()
        }
    let rewriteParentStep : ScmRewriteFunction<unit> = scmRewrite {
            //here instead of "step subcomponent" the converted step must be called
            return ()
        }
    let rewriteProvPort : ScmRewriteFunction<unit> = scmRewrite {
            // replace reqPorts and fields by their proper names, replace Fault Expressions
            // caution: also take care, that no local var name has by accident the name of a _new_ field
            
            return ()
        }
    let rewriteFaults : ScmRewriteFunction<unit> = scmRewrite {
            // replace reqPorts and fields by their proper names, replace Fault Expressions
            // caution: also take care, that no local var name has by accident the name of a _new_ field
            
            return ()
        }
    let assertSubcomponentEmpty : ScmRewriteFunction<unit> = scmRewrite {
            return ()
        }
    let removeSubComponent : ScmRewriteFunction<unit> = scmRewrite {
            return ()
        }        
    let writeBackChangesIntoModel  : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            if (state.ChangedSubcomponents.IsNone) then
                // do not modify old tainted state here
                return! putState state // (alternative is to "return ()"
            else
                let changedSubcomponents = state.ChangedSubcomponents.Value
                let newModel = state.Model.replaceDescendant changedSubcomponents.ParentPath changedSubcomponents.ParentCompDecl
                let modifiedState =
                    { state with
                        ScmRewriteState.Model = newModel;
                        //ScmRewriteState.ChangedSubcomponents = None; ///???
                        ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                    }
                return! putState modifiedState
        }
    let assertNoSubcomponent : ScmRewriteFunction<unit> = scmRewrite {
            return ()
        }
        
    let inlineMainStep : ScmRewriteFunction<unit> = scmRewrite {
            return ()
        }
    let levelUpSubcomponent : ScmRewriteFunction<unit> = scmRewrite {
            // idea: first level up every item of a component,
            //       then rewrite every code accessing to some specific element of it
            do! selectSubComponent
            do! scmRewriteFixpoint {do! levelUpField} //Invariant: Imagine ChangedSubcomponents are written back into model. Fieldaccess (read/write) is either on the "real" field or on a "forwarded field" (map entry in ArtificialFieldsOldToNew exists, and new field exists)
            do! scmRewriteFixpoint {do! levelUpFault}
            do! scmRewriteFixpoint {do! convertStepToPort}
            do! scmRewriteFixpoint {do! levelUpReqPort}
            do! scmRewriteFixpoint {do! levelUpProvPort}
            do! scmRewriteFixpoint {do! levelUpAndRewriteBinding}
            do! scmRewriteFixpoint {do! rewriteParentStep}
            do! scmRewriteFixpoint {do! rewriteProvPort}
            do! scmRewriteFixpoint {do! rewriteFaults}
            do! assertSubcomponentEmpty
            do! removeSubComponent
            do! writeBackChangesIntoModel
        }

    // here the workflow, which defines a globalglobal rewrite rule, whic
    let levelUpWorkflow =
        let s : ScmRewriteFunction<unit> =
            scmRewrite {
                do! scmRewriteFixpoint {do! levelUpSubcomponent}
                do! assertNoSubcomponent
                do! inlineMainStep
            }
        runState s

