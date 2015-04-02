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
    open ScmWorkflow

    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Change Subcomponent
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
        

    type IScmChangeSubcomponent<'state when 'state :> IScmModel<'state>> =
        interface
            abstract getPathOfChangingSubcomponent : CompPath
            abstract setPathOfChangingSubcomponent : CompPath -> 'state
        end

        
    type IScmChangeSubcomponentWithTracing<'state,'source when 'state :> IScmModel<'state>
                                                           and 'state :> IScmChangeSubcomponent<'state>
                                                           and 'source : comparison> =
        'state * TraceableModel.TracingInfo<'source,StateVar>
         
    type IScmChangeSubcomponentWorkflowFunction<'state,'source,'returnType when 'state :> IScmModel<'state>
                                                                            and 'state :> IScmChangeSubcomponent<'state>
                                                                            and 'source : comparison> =
        WorkflowFunction<IScmChangeSubcomponentWithTracing<'state,'source>,
                         IScmChangeSubcomponentWithTracing<'state,'source>,
                         'returnType>
        

    let getSubComponentToChange<'state,'source when 'state :> IScmModel<'state>
                                                      and 'state :> IScmChangeSubcomponent<'state>
                                                      and 'source : comparison>
             : IScmChangeSubcomponentWorkflowFunction<'state,'source,CompDecl> = workflow {
        let! state = TraceableModel.getModel
        let model = state.getModel
        let rootComp = match model with | ScmModel(rootComp) -> rootComp
        let path = state.getPathOfChangingSubcomponent
        return (rootComp.getDescendantUsingPath path)
    }
                
    // example with exact type annotation without workflow-surrounding (also easily implementable with workflow {})
    let getPathOfSubComponentToChange<'state,'source when 'state :> IScmModel<'state>
                                                      and 'state :> IScmChangeSubcomponent<'state>
                                                      and 'source : comparison>
               : WorkflowFunction<'state * TraceableModel.TracingInfo<'source,StateVar>,
                                  'state * TraceableModel.TracingInfo<'source,StateVar>,
                                  CompPath> =
        let getPathOfSubComponentToChange ( workflowState : WorkflowState<'state * TraceableModel.TracingInfo<'source,StateVar>>
                                                                     when 'state :> IScmChangeSubcomponent<'state>)
               : (CompPath * (WorkflowState<'state * TraceableModel.TracingInfo<'source,StateVar>>) ) =
            let state,oldTracingInfo = workflowState.State            
            (state.getPathOfChangingSubcomponent,workflowState)
        WorkflowFunction (getPathOfSubComponentToChange)

    let updateSubComponentToChange (updatedSubComponent:CompDecl) : IScmChangeSubcomponentWorkflowFunction<_,_,unit> = workflow {
        let! state = TraceableModel.getModel
        let model = state.getModel
        let rootComp = match model with | ScmModel(rootComp) -> rootComp
        let path = state.getPathOfChangingSubcomponent
        let newRootComp = rootComp.replaceDescendant path updatedSubComponent
        let newState = state.setModel (ScmModel(newRootComp))
        do! TraceableModel.setModel newState
    }
        
    
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Fresh Names
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    type IFreshNameDepot<'state> =
        interface
            abstract getTakenNames : Set<string>
            abstract setTakenNames : Set<string> -> 'state //must be implemented by every state
        end
        
    type IFreshNameDepotWithTracing<'state,'source when 'state :> IScmModel<'state>
                                                    and 'state :> IFreshNameDepot<'state>
                                                    and 'source : comparison> =
        'state * TraceableModel.TracingInfo<'source,StateVar>
         
    type IFreshNameDepotWorkflowFunction<'state,'source,'returnType when 'state :> IScmModel<'state>
                                                                     and 'state :> IFreshNameDepot<'state>
                                                                     and 'source : comparison> =
        WorkflowFunction<IFreshNameDepotWithTracing<'state,'source>,
                         IFreshNameDepotWithTracing<'state,'source>,
                         'returnType>

    let getCompletlyFreshName (basedOn:string) : IFreshNameDepotWorkflowFunction<_,_,string> = workflow {
            let! state = TraceableModel.getModel
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
            do! TraceableModel.setModel modifiedState
            return newName
        }

    let getUnusedFieldName (basedOn:string) : IFreshNameDepotWorkflowFunction<_,_,Field> = workflow {
            let! name = getCompletlyFreshName basedOn
            return Field(name)
        }

    let getUnusedFaultName (basedOn:string) : IFreshNameDepotWorkflowFunction<_,_,Fault> = workflow {
            let! name = getCompletlyFreshName basedOn
            return Fault.Fault(name)
        }
            
    let getUnusedReqPortName (basedOn:string) : IFreshNameDepotWorkflowFunction<_,_,ReqPort> = workflow {
            let! name = getCompletlyFreshName basedOn
            return ReqPort(name)
        }

    let getUnusedProvPortName  (basedOn:string) : IFreshNameDepotWorkflowFunction<_,_,ProvPort> = workflow {
            let! name = getCompletlyFreshName basedOn
            return ProvPort(name)
        }
        
    let getUnusedVarName (basedOn:string) : IFreshNameDepotWorkflowFunction<_,_,Var> = workflow {
            let! name = getCompletlyFreshName basedOn
            return Var(name)
        }

    let getUnusedVarNames<'state,'source when 'state :> IScmModel<'state>
                                          and 'state :> IFreshNameDepot<'state>
                                          and 'source : comparison>
                          (basedOn:string list) : IFreshNameDepotWorkflowFunction<'state,'source,Var list> =

        let newUnusedVarNames (workflowState:WorkflowState<IFreshNameDepotWithTracing<'state,'source>>)
                : (Var list * WorkflowState<IFreshNameDepotWithTracing<'state,'source>>) =
            let mutable varState = workflowState
            let mutable newVars = []
            for i in basedOn do
                let (newVar,newWorkflowState) = runWorkflowState (getUnusedVarName i) varState
                varState <- newWorkflowState
                newVars <- newVar::newVars
            (List.rev newVars, varState)
        WorkflowFunction (newUnusedVarNames)

    let getUnusedFieldNames<'state,'source when 'state :> IScmModel<'state>
                                          and 'state :> IFreshNameDepot<'state>
                                          and 'source : comparison>
                          (basedOn:string list) : IFreshNameDepotWorkflowFunction<'state,'source,Field list> =

        let newUnusedFieldNames (workflowState:WorkflowState<IFreshNameDepotWithTracing<'state,'source>>)
                : (Field list * WorkflowState<IFreshNameDepotWithTracing<'state,'source>>) =
            let mutable varState = workflowState
            let mutable newFields = []
            for i in basedOn do
                let (newField,newWorkflowState) = runWorkflowState (getUnusedFieldName i) varState
                varState <- newWorkflowState
                newFields <- newField::newFields
            (List.rev newFields, varState)
        WorkflowFunction (newUnusedFieldNames)

        


        
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Check Consistency
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    let checkConsistency<'state> : WorkflowFunction<'state,'state,bool> = workflow {
            return true
        }
    
