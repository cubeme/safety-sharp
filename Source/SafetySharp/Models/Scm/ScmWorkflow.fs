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

module internal ScmWorkflow =
    open SafetySharp.Workflow
    open Scm
        
    type IScmModel<'state> =
        interface
            inherit IModel<Traceable> 
            abstract getModel : ScmModel
            abstract setModel : ScmModel -> 'state
            
            abstract getUncommittedForwardTracerMap : Map<Traceable,Traceable> //to be able to inherit uncommitted traces
            abstract setUncommittedForwardTracerMap : Map<Traceable,Traceable> -> 'state //used to commit
        end

    type IScmModelWorkflowFunction<'state,'traceableOfOrigin,'returnType when 'state :> IScmModel<'state>> =
        EndogenousWorkflowFunction<'state,'traceableOfOrigin,Traceable,'returnType>
                

    let iscmGetModel<'traceableOfOrigin,'state when 'state :> IScmModel<'state>> () : IScmModelWorkflowFunction<'state,'traceableOfOrigin,ScmModel> = workflow {
        let! iscmModel = getState ()
        let model = iscmModel.getModel
        return model
    }    
    
    let iscmSetModel<'traceableOfOrigin,'state when 'state :> IScmModel<'state>> (model:ScmModel) : IScmModelWorkflowFunction<'state,'traceableOfOrigin,unit> = workflow {
        let! iscmModel = getState ()
        let newIscmModel = iscmModel.setModel model
        do! updateState newIscmModel
    }

    let iscmSetUncommittedForwardTracerMap<'traceableOfOrigin,'state when 'state :> IScmModel<'state>> (newUncommittedForwardTracerMap:Map<Traceable,Traceable>) : IScmModelWorkflowFunction<'state,'traceableOfOrigin,unit> = workflow {
        let! iscmModel = getState ()
        let newIscmModel = iscmModel.setUncommittedForwardTracerMap newUncommittedForwardTracerMap
        do! updateState newIscmModel
    }    

    let iscmGetUncommittedForwardTracerMap<'traceableOfOrigin,'state when 'state :> IScmModel<'state>> () : IScmModelWorkflowFunction<'state,'traceableOfOrigin,Map<Traceable,Traceable>> = workflow {
        let! iscmModel = getState ()
        let uncommittedForwardTracerMap = iscmModel.getUncommittedForwardTracerMap
        return uncommittedForwardTracerMap
    } 
    
    let iscmTraceTraceable<'traceableOfOrigin,'state when 'state :> IScmModel<'state>> (_from:Traceable) (_to:Traceable) : IScmModelWorkflowFunction<'state,'traceableOfOrigin,unit> = workflow {
        let! uncommittedForwardTracerMap = iscmGetUncommittedForwardTracerMap ()
        let newUncommittedForwardTracerMap =
            if uncommittedForwardTracerMap.ContainsKey _from then
                failwith "BUG: There exists already an entry for this traceable. The traceable is not unique. Maybe because there was a name clash."
            uncommittedForwardTracerMap.Add(_from,_to)
        do! iscmSetUncommittedForwardTracerMap newUncommittedForwardTracerMap
    }    

    let iscmCommitForwardTracerMap<'traceableOfOrigin,'state when 'state :> IScmModel<'state>> () : IScmModelWorkflowFunction<'state,'traceableOfOrigin,unit> = workflow {
        let! iscmModel = getState ()

        let forwardTracerMapInClosure = iscmModel.getUncommittedForwardTracerMap
        let intermediateTracer (oldValue:Traceable) =
            let rec findValue (oldValue:Traceable) =
                if forwardTracerMapInClosure.ContainsKey oldValue then
                    findValue (forwardTracerMapInClosure.Item oldValue)
                else
                    oldValue
            findValue oldValue
        
        let emptyUncommittedTracerMap = Map.empty<Traceable,Traceable>
        let newIscmModel = iscmModel.setUncommittedForwardTracerMap emptyUncommittedTracerMap

        do! updateState newIscmModel
        do! updateTracer intermediateTracer
    }
    
    let scmGetModel () : EndogenousWorkflowFunction<Scm.ScmModel,_,Traceable,Scm.ScmModel> = workflow {
        let! model = getState ()
        return model
    }

    let scmSetModel<'oldIrrelevantState> (model:ScmModel)
            : ExogenousWorkflowFunction<'oldIrrelevantState,ScmModel,_,_,Traceable,unit> = workflow {
        do! updateState model
    }

    type PlainScmModel(model:ScmModel,forwardTracerMap:Map<Traceable,Traceable>) =
        class end
            with
                member this.getModel : ScmModel = model
                interface IScmModel<PlainScmModel> with
                    member this.getTraceables =
                        let imodel = this.getModel :> IModel<Traceable>
                        imodel.getTraceables
                    member this.getModel : ScmModel = model
                    member this.setModel (model:ScmModel) = PlainScmModel(model,forwardTracerMap)
                    member this.getUncommittedForwardTracerMap : Map<Traceable,Traceable> = forwardTracerMap
                    member this.setUncommittedForwardTracerMap (forwardTracerMap:Map<Traceable,Traceable>) = PlainScmModel(model,forwardTracerMap)
    
    type PlainScmModelWorkflowFunction<'traceableOfOrigin,'returnType> =
        EndogenousWorkflowFunction<PlainScmModel,'traceableOfOrigin,Traceable,'returnType>
        
       
    let setInitialPlainModelState (model:ScmModel) : LoadWorkflowFunction<_,PlainScmModel,Traceable,unit> = workflow {
        do! initializeTracer (model.getTraceables)
        let emptyUncommittedTracerMap = Map.empty<Traceable,Traceable>
        do! updateState (PlainScmModel(model,emptyUncommittedTracerMap))
    }
    
    let setPlainModelState (model:ScmModel) (uncommittedTracerMap:Map<Traceable,Traceable>) = workflow {
        do! updateState (PlainScmModel(model,uncommittedTracerMap))
    }
    
    let iscmToPlainModelState<'state,'traceableOfOrigin when 'state :> IScmModel<'state>> ()
            : ExogenousWorkflowFunction<'state,PlainScmModel,'traceableOfOrigin,Traceable,Traceable,unit> = workflow {
        let! state = getState ()
        do! setPlainModelState state.getModel state.getUncommittedForwardTracerMap //inherit uncommitted traces
    }
    
    let scmToPlainModelState ()
            : ExogenousWorkflowFunction<ScmModel,PlainScmModel,_,Traceable,Traceable,unit> = workflow {
        let! state = getState ()
        let emptyUncommittedTracerMap = Map.empty<Traceable,Traceable>
        do! setPlainModelState state emptyUncommittedTracerMap
    }
        
    let iscmToScmState<'state,'traceableOfOrigin when 'state :> IScmModel<'state>> ()
            : ExogenousWorkflowFunction<'state,ScmModel,'traceableOfOrigin,Traceable,Traceable,unit> = workflow {
        let! state = getState ()
        do! iscmCommitForwardTracerMap ()
        do! SafetySharp.Workflow.updateState state.getModel
    }
    