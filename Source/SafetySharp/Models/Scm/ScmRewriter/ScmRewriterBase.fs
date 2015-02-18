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
open SafetySharp.Models.ScmHelpers
open SafetySharp.Workflow

module internal ScmRewriterBase =
    
    type ScmModel = CompDecl //may change, but I hope it does not
                       
    (*
    type ScmRewriteState<'subState> = {
        Model : ScmModel;

        ChangingSubComponent : CompDecl;
        PathOfChangingSubcomponent : CompPath;

        TakenNames : Set<string>;
        SubState : 'subState;
    }
        with
            static member initial (scm:ScmModel) (subState:'subState) = 
                {
                    ScmRewriteState.Model = scm;
                    ChangingSubComponent = scm;
                    PathOfChangingSubcomponent = [scm.Comp];
                    ScmRewriteState.TakenNames = scm.getTakenNames () |> Set.ofList;
                    ScmRewriteState.SubState = subState;
                }
            member this.deriveWithSubState<'newSubState> (newSubState:'newSubState) =
                {
                    ScmRewriteState.Model = this.Model;
                    ScmRewriteState.ChangingSubComponent = this.ChangingSubComponent;
                    ScmRewriteState.PathOfChangingSubcomponent = this.PathOfChangingSubcomponent;
                    ScmRewriteState.TakenNames = this.TakenNames;
                    ScmRewriteState.SubState = newSubState; //<---- everything but this must be changed
                }


    type ScmRewriteSimpleState = ScmRewriteState<unit> //simple state is a state without subState
                    
    let initialSimpleState (scm:ScmModel) = ScmRewriteState<unit>.initial scm ()
    *)


    
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Scm-Model
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    type IScmModel<'state> =
        interface
            abstract getModel : ScmModel
            abstract setModel : ScmModel -> 'state
        end
        

    let getModel<'state when 'state :> IScmModel<'state>> : WorkflowFunction<'state,'state,CompDecl> = workflow {
        let! state = getState
        let model = state.getModel
        return model
    }

    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Change Subcomponent
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
        

    type IScmChangeSubcomponent<'state when 'state :> IScmModel<'state>> =
        interface
            abstract getPathOfChangingSubcomponent : CompPath
            abstract setPathOfChangingSubcomponent : CompPath -> 'state
        end
        

    let getSubComponentToChange<'state when 'state :> IScmChangeSubcomponent<'state>> : WorkflowFunction<'state,'state,CompDecl> = workflow {
        let! state = getState
        let model = state.getModel
        let path = state.getPathOfChangingSubcomponent
        return (model.getDescendantUsingPath path)
    }
                
    // example with exact type annotation without workflow-surrounding (also easily implementable with workflow {})
    let getPathOfSubComponentToChange<'state when 'state :> IScmChangeSubcomponent<'state>> : WorkflowFunction<'state,'state,CompPath> =
        let getPathOfSubComponentToChange (state:WorkflowState<'state> when 'state :> IScmChangeSubcomponent<'state>) : (CompPath * WorkflowState<'state>) =            
            state.State.getPathOfChangingSubcomponent,state
        WorkflowFunction (getPathOfSubComponentToChange)

    let updateSubComponentToChange<'state when 'state :> IScmChangeSubcomponent<'state>> (updatedSubComponent:CompDecl) : WorkflowFunction<'state,'state,unit> = workflow {
        let! state = getState
        let model = state.getModel
        let path = state.getPathOfChangingSubcomponent
        let newModel = model.replaceDescendant path updatedSubComponent
        let newState = state.setModel newModel
        do! updateState newState
    }
        
    
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Fresh Names
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    type IFreshNameDepot<'state> =
        interface
            abstract getTakenNames : Set<string>
            abstract setTakenNames : Set<string> -> 'state //must be implemented by every state
        end

    let getCompletlyFreshName<'state when 'state :> IFreshNameDepot<'state>> (basedOn:string) : WorkflowFunction<'state,'state,string> = workflow {
            let! state = getState
            let newName = 
                let existsName (nameCandidate:string) : bool =
                    state.getTakenNames.Contains nameCandidate
                let rec inventName numberSuffix : string =
                    // If desired name does not exist, get name with the lowest numberSuffix.
                    // This is not really beautiful, but finally leads to a free name, (because domain is finite).
                    let nameCandidate = sprintf "%s_art%i" basedOn numberSuffix
                    if existsName nameCandidate = false then
                        nameCandidate
                    else
                        inventName (numberSuffix+1)
                if existsName basedOn = false then
                    basedOn
                else
                    inventName 0
            let modifiedState = state.setTakenNames (state.getTakenNames.Add newName)
            return! updateStateAndReturn modifiedState newName
        }

    let getUnusedFieldName<'state when 'state :> IFreshNameDepot<'state>> (basedOn:string) : WorkflowFunction<'state,'state,Field> = workflow {
            let! name = getCompletlyFreshName basedOn
            return Field(name)
        }

    let getUnusedFaultName<'state when 'state :> IFreshNameDepot<'state>> (basedOn:string) : WorkflowFunction<'state,'state,Fault> = workflow {
            let! name = getCompletlyFreshName basedOn
            return Fault.Fault(name)
        }
            
    let getUnusedReqPortName<'state when 'state :> IFreshNameDepot<'state>> (basedOn:string) : WorkflowFunction<'state,'state,ReqPort> = workflow {
            let! name = getCompletlyFreshName basedOn
            return ReqPort(name)
        }

    let getUnusedProvPortName<'state when 'state :> IFreshNameDepot<'state>> (basedOn:string) : WorkflowFunction<'state,'state,ProvPort> = workflow {
            let! name = getCompletlyFreshName basedOn
            return ProvPort(name)
        }
        
    let getUnusedVarName<'state when 'state :> IFreshNameDepot<'state>> (basedOn:string) : WorkflowFunction<'state,'state,Var> = workflow {
            let! name = getCompletlyFreshName basedOn
            return Var(name)
        }

    let getUnusedVarNames<'state when 'state :> IFreshNameDepot<'state>> (basedOn:string list) : WorkflowFunction<'state,'state,Var list> =
        let newUnusedVarNames (state) : (Var list * WorkflowState<'state>) =
            let mutable varState = state
            let mutable newVars = []
            for i in basedOn do
                let (newVar,newState) = runWorkflowState (getUnusedVarName i) varState
                varState <- newState
                newVars <- newVar::newVars
            (List.rev newVars, varState)
        WorkflowFunction (newUnusedVarNames)

    let getUnusedFieldNames<'state when 'state :> IFreshNameDepot<'state>> (basedOn:string list) : WorkflowFunction<'state,'state,Field list> =
        let newUnusedFieldNames (state) : (Field list * WorkflowState<'state>) =
            let mutable varState = state
            let mutable newFields = []
            for i in basedOn do
                let (newField,newState) = runWorkflowState (getUnusedFieldName i) varState
                varState <- newState
                newFields <- newField::newFields
            (List.rev newFields, varState)
        WorkflowFunction (newUnusedFieldNames)

        


        
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Check Consistency
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    let checkConsistency<'state> : WorkflowFunction<'state,'state,bool> = workflow {
            return true
        }
    
