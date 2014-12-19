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
        Tainted : bool;
    }
        with
            static member initial (scm:ScmModel) = 
                {
                    ScmRewriteState.Model = scm;
                    ScmRewriteState.ComponentToRemove = None;
                    ScmRewriteState.Tainted = false;
                }
                
    type ScmRewriteFunction<'a> = ScmRewriteFunction of (ScmRewriteState -> 'a * ScmRewriteState)
    
    // TODO:
    //   - RewriteElement should return, if it made a change
    //   - smallest element only gets called once
    //   - liftToFixpoint repeats a small element, until it doesn't change something anymore
    //   - so levelUpField levels up one field, levelUpFields levels up fields, until nothing possible anymore


    let runState (ScmRewriteFunction s) a = s a
    let getState = ScmRewriteFunction (fun s -> (s,s))
    let putState s = ScmRewriteFunction (fun _ -> ((),s))

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
    //TODO: let scmRewriteFixpoint = new ScmRewriteFixpoint. (fixpoint Computation Expression. Repeat something, until fixpoint is reached)


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
                    let field = childCompDecl.Fields.Head
                    let newChildCompDecl = childCompDecl.removeField field
                    let transformedField = field //TODO: ensure unique name. Add forwarder. Add mapping between old and new field
                    
                    let newParentCompDecl = parentCompDecl.replaceChild(childCompDecl,newChildCompDecl)
                                                          .addField(transformedField)
                    let newModel = state.Model.replaceDescendant parentPath newParentCompDecl
                    let modifiedState =
                        { state with
                            ScmRewriteState.Model = newModel;
                            ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                        }
                    return! putState modifiedState
        }

    let levelUpSubcomponent : ScmRewriteFunction<unit> = scmRewrite {
            do! levelUpField
        }

    // here the workflow, which defines a globalglobal rewrite rule, whic
    let levelUpWorkflow =
        let s : ScmRewriteFunction<unit> =
            scmRewrite {
                do! levelUpSubcomponent
            }
        runState s
(*

Requirements
* Generic
    - A rule _must_ change something (otherwise infinite execution)
    - Unfinished Element
* Rules
    - Identify some parts
    - Only read some parts
    - Modify some parts
* Helpers
    - Concatenation of Lists
* Subrules
    - List of things to do, before a target is really "written"

Later:
 - F# Type Provider, which offers a K-like way to define rules
 - Rule-Apply-Strategy e.g. [Rule1*,[Rule2*,Rule3*]*]*
 - Taint-Flag, if a rule could be applied


Example:
 - 


*)

