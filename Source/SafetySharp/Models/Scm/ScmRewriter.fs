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
    
    type ScmRewriteState = {
        Model : ScmModel;
        ComponentToRemove : (Comp list) option;
        // Forwarder
        ArtificialFieldsOldToNew : Map<FieldPath,FieldPath> //Map from old path to new path (TODO: when not necessary, delete)
        ArtificialFieldsNewToOld : Map<FieldPath,FieldPath> //Map from new path to old path (TODO: when not necessary, delete)
        // Flag, which determines, if something was changed (needed for fixpoint iteration)
        Tainted : bool;
    }
        with
            static member initial (scm:ScmModel) = 
                {
                    ScmRewriteState.Model = scm;
                    ScmRewriteState.ComponentToRemove = None;
                    ScmRewriteState.ArtificialFieldsOldToNew = Map.empty<FieldPath,FieldPath>;
                    ScmRewriteState.ArtificialFieldsNewToOld = Map.empty<FieldPath,FieldPath>;
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
    let levelUpField : ScmRewriteFunction<unit> = scmRewrite {
            let! state = getState
            if (state.ComponentToRemove.IsNone) then
                // do not modify old tainted state here
                return! putState state
            else
                let childPath = state.ComponentToRemove.Value
                let parentPath = state.ComponentToRemove.Value.Tail
                let childCompDecl = state.Model.getDescendantUsingPath childPath
                let parentCompDecl = state.Model.getDescendantUsingPath parentPath
                // parent is target, child is source
                if childCompDecl.Fields.IsEmpty then
                    // do not modify old tainted state here
                    return! putState state
                else
                    let fieldDecl = childCompDecl.Fields.Head
                    let field = fieldDecl.Field
                    let newChildCompDecl = childCompDecl.removeField field
                    let transformedField = parentCompDecl.getUnusedFieldName (sprintf "%s_%s" childCompDecl.getName field.getName)
                    let transformedFieldDecl = 
                        {fieldDecl with
                            FieldDecl.Field = transformedField;
                        }                    
                    let newParentCompDecl = parentCompDecl.replaceChild(childCompDecl,newChildCompDecl)
                                                          .addField(transformedFieldDecl)
                    let newModel = state.Model.replaceDescendant parentPath newParentCompDecl
                    let modifiedState =
                        { state with
                            ScmRewriteState.Model = newModel;
                            ScmRewriteState.ArtificialFieldsOldToNew = state.ArtificialFieldsOldToNew.Add( (childPath,field), (parentPath,transformedField) );
                            ScmRewriteState.ArtificialFieldsNewToOld = state.ArtificialFieldsNewToOld.Add( (parentPath,transformedField), (childPath,field) );
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
        }
        
    let selectSubComponent : ScmRewriteFunction<unit> = scmRewrite {
            return ()
        }
    let levelUpFault : ScmRewriteFunction<unit> = scmRewrite {
            return ()
        }
    let levelUpReqPort : ScmRewriteFunction<unit> = scmRewrite {
            return ()
        }
    let levelUpProvPort : ScmRewriteFunction<unit> = scmRewrite {
            return ()
        }
    let levelUpAndRewriteBinding : ScmRewriteFunction<unit> = scmRewrite {
            return ()
        }
    let convertStepToPort : ScmRewriteFunction<unit> = scmRewrite {
            // replace step to required port and provided port and binding, add a link from subcomponent path to new required port
            return ()
        }
    let rewriteParentStep : ScmRewriteFunction<unit> = scmRewrite {
            //here instead of "step subcomponent" the converted step must be called
            return ()
        }
    let rewriteProvPort : ScmRewriteFunction<unit> = scmRewrite {
            // replace reqPorts and fields by their proper names
            return ()
        }
    let assertSubcomponentEmpty : ScmRewriteFunction<unit> = scmRewrite {
            return ()
        }
    let removeSubComponent : ScmRewriteFunction<unit> = scmRewrite {
            return ()
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
            do! scmRewriteFixpoint {do! levelUpField}
            do! scmRewriteFixpoint {do! levelUpFault}
            do! scmRewriteFixpoint {do! convertStepToPort}
            do! scmRewriteFixpoint {do! levelUpReqPort}
            do! scmRewriteFixpoint {do! levelUpProvPort}
            do! scmRewriteFixpoint {do! levelUpAndRewriteBinding}
            do! scmRewriteFixpoint {do! rewriteParentStep}
            do! scmRewriteFixpoint {do! rewriteProvPort}
            do! assertSubcomponentEmpty
            do! removeSubComponent
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

