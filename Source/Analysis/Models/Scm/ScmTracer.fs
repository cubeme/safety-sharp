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

module internal ScmTracer =
    open SafetySharp.Workflow
    open SafetySharp.ITracing
    open Scm
    open ScmHelpers
        
    type IScmTracer<'traceableOfOrigin,'state> =
        interface
            inherit ITracing<ScmModel,'traceableOfOrigin,Traceable,'state> 
            abstract setModel : ScmModel -> 'state
            
            abstract getUncommittedForwardTracerMap : Map<Traceable,Traceable> //to be able to inherit uncommitted traces
            abstract setUncommittedForwardTracerMap : Map<Traceable,Traceable> -> 'state //used to commit
        end

    type IScmTracerWorkflowFunction<'state,'traceableOfOrigin,'returnType when 'state :> IScmTracer<'traceableOfOrigin,'state>> =
        WorkflowFunction<'state,'state,'returnType>                

    let iscmGetModel<'traceableOfOrigin,'state when 'state :> IScmTracer<'traceableOfOrigin,'state>> () : IScmTracerWorkflowFunction<'state,'traceableOfOrigin,ScmModel> = workflow {
        let! iScmTracer = getState ()
        let model = iScmTracer.getModel
        return model
    }    
    
    let iscmSetModel<'traceableOfOrigin,'state when 'state :> IScmTracer<'traceableOfOrigin,'state>> (model:ScmModel) : IScmTracerWorkflowFunction<'state,'traceableOfOrigin,unit> = workflow {
        let! iScmTracer = getState ()
        let newIScmTracer = iScmTracer.setModel model
        do! updateState newIScmTracer
    }

    let iscmSetUncommittedForwardTracerMap<'traceableOfOrigin,'state when 'state :> IScmTracer<'traceableOfOrigin,'state>> (newUncommittedForwardTracerMap:Map<Traceable,Traceable>) : IScmTracerWorkflowFunction<'state,'traceableOfOrigin,unit> = workflow {
        let! iScmTracer = getState ()
        let newIScmTracer = iScmTracer.setUncommittedForwardTracerMap newUncommittedForwardTracerMap
        do! updateState newIScmTracer
    }    

    let iscmGetUncommittedForwardTracerMap<'traceableOfOrigin,'state when 'state :> IScmTracer<'traceableOfOrigin,'state>> () : IScmTracerWorkflowFunction<'state,'traceableOfOrigin,Map<Traceable,Traceable>> = workflow {
        let! iScmTracer = getState ()
        let uncommittedForwardTracerMap = iScmTracer.getUncommittedForwardTracerMap
        return uncommittedForwardTracerMap
    } 

    let iscmGetTraceablesOfOrigin<'traceableOfOrigin,'state when 'state :> IScmTracer<'traceableOfOrigin,'state>> () : IScmTracerWorkflowFunction<'state,'traceableOfOrigin,'traceableOfOrigin list> = workflow {
        let! iScmTracer = getState ()
        let traceablesOfOrigin = iScmTracer.getTraceablesOfOrigin
        return traceablesOfOrigin
    } 

    let iscmGetForwardTracer<'traceableOfOrigin,'state when 'state :> IScmTracer<'traceableOfOrigin,'state>> () : IScmTracerWorkflowFunction<'state,'traceableOfOrigin,('traceableOfOrigin -> Traceable)> = workflow {
        let! iScmTracer = getState ()
        let forwardTracer = iScmTracer.getForwardTracer
        return forwardTracer
    } 
    
    let iscmTraceTraceable<'traceableOfOrigin,'state when 'state :> IScmTracer<'traceableOfOrigin,'state>> (_from:Traceable) (_to:Traceable) : IScmTracerWorkflowFunction<'state,'traceableOfOrigin,unit> = workflow {
        let! uncommittedForwardTracerMap = iscmGetUncommittedForwardTracerMap ()
        let newUncommittedForwardTracerMap =
            if uncommittedForwardTracerMap.ContainsKey _from then
                failwith "BUG: There exists already an entry for this traceable. The traceable is not unique. Maybe because there was a name clash."
            uncommittedForwardTracerMap.Add(_from,_to)
        do! iscmSetUncommittedForwardTracerMap newUncommittedForwardTracerMap
    }    

    let iscmCommitForwardTracerMap<'traceableOfOrigin,'state when 'state :> IScmTracer<'traceableOfOrigin,'state>> () : IScmTracerWorkflowFunction<'state,'traceableOfOrigin,unit> = workflow {
        let! iScmTracer = getState ()

        let forwardTracerMapInClosure = iScmTracer.getUncommittedForwardTracerMap
        let newForwardTracer (originValue:'traceableOfOrigin) =
            let oldValue = iScmTracer.getForwardTracer (originValue)
            let rec findValue (oldValue:Traceable) =
                if forwardTracerMapInClosure.ContainsKey oldValue then
                    findValue (forwardTracerMapInClosure.Item oldValue)
                else
                    oldValue
            findValue oldValue
        
        let emptyUncommittedTracerMap = Map.empty<Traceable,Traceable>
        let newIScmTracer = iScmTracer.setUncommittedForwardTracerMap emptyUncommittedTracerMap
        let newIScmTracer = newIScmTracer.setForwardTracer newForwardTracer
        do! updateState newIScmTracer
    }
    
    let scmGetModel () : WorkflowFunction<Scm.ScmModel,Scm.ScmModel,Scm.ScmModel> = workflow {
        let! model = getState ()
        return model
    }

    let scmSetModel<'oldIrrelevantState> (model:ScmModel)
            : ExogenousWorkflowFunction<'oldIrrelevantState,Scm.ScmModel> = workflow {
        do! updateState model
    }

    type SimpleScmTracer<'traceableOfOrigin> = {
            Model:ScmModel;
            UncommitedForwardTracerMap:Map<Traceable,Traceable>;
            TraceablesOfOrigin : 'traceableOfOrigin list;
            ForwardTracer : 'traceableOfOrigin -> Traceable;
        }
            with

                member this.getModel : ScmModel = this.Model
                interface IScmTracer<'traceableOfOrigin,SimpleScmTracer<'traceableOfOrigin>> with
                    member this.getModel : ScmModel = this.Model
                    member this.setModel (model:ScmModel) = {this with Model=model}
                    member this.getUncommittedForwardTracerMap : Map<Traceable,Traceable> = this.UncommitedForwardTracerMap
                    member this.setUncommittedForwardTracerMap (forwardTracerMap:Map<Traceable,Traceable>) = {this with UncommitedForwardTracerMap=forwardTracerMap}
                    member this.getTraceablesOfOrigin : 'traceableOfOrigin list = this.TraceablesOfOrigin
                    member this.setTraceablesOfOrigin (traceableOfOrigin:('traceableOfOrigin list)) = {this with TraceablesOfOrigin=traceableOfOrigin}
                    member this.getForwardTracer : ('traceableOfOrigin -> Traceable) = this.ForwardTracer
                    member this.setForwardTracer (forwardTracer:('traceableOfOrigin -> Traceable)) = {this with ForwardTracer=forwardTracer}
                    member this.getTraceables : Traceable list =
                        this.Model.getTraceables

    
    type SimpleScmTracerWorkflowFunction<'traceableOfOrigin,'returnType> =
        WorkflowFunction<SimpleScmTracer<'traceableOfOrigin>,SimpleScmTracer<'traceableOfOrigin>,'returnType>
        
       
    let setInitialSimpleScmTracer<'oldIrrelevantState> (model:ScmModel)
            : WorkflowFunction<'oldIrrelevantState,SimpleScmTracer<Traceable>,unit> = workflow {
        let emptyUncommittedTracerMap = Map.empty<Traceable,Traceable>
        let scmTracer =
            {
                SimpleScmTracer.Model = model;
                SimpleScmTracer.UncommitedForwardTracerMap = emptyUncommittedTracerMap;
                SimpleScmTracer.TraceablesOfOrigin = model.getTraceables;
                SimpleScmTracer.ForwardTracer = id;
            }
        do! updateState scmTracer
    }
        
    let iscmToSimpleScmTracer<'state,'traceableOfOrigin when 'state :> IScmTracer<'traceableOfOrigin,'state>> ()
            : ExogenousWorkflowFunction<'state,SimpleScmTracer<'traceableOfOrigin>> = workflow {
        let! state = getState ()
        let scmTracer =
            {
                SimpleScmTracer.Model = state.getModel;
                SimpleScmTracer.UncommitedForwardTracerMap = state.getUncommittedForwardTracerMap;  //inherit uncommitted traces
                SimpleScmTracer.TraceablesOfOrigin = state.getTraceablesOfOrigin;
                SimpleScmTracer.ForwardTracer = state.getForwardTracer;
            }
        do! updateState scmTracer
    }
    
    let scmToSimpleScmTracer () : ExogenousWorkflowFunction<ScmModel,SimpleScmTracer<Scm.Traceable>> = workflow {
        let! model = getState ()        
        let emptyUncommittedTracerMap = Map.empty<Traceable,Traceable>
        let scmTracer =
            {
                SimpleScmTracer.Model = model;
                SimpleScmTracer.UncommitedForwardTracerMap = emptyUncommittedTracerMap;
                SimpleScmTracer.TraceablesOfOrigin = model.getTraceables;
                SimpleScmTracer.ForwardTracer = id;
            }
        do! updateState scmTracer
    }
        
    let iscmToScmState<'state,'traceableOfOrigin when 'state :> IScmTracer<'traceableOfOrigin,'state>> ()
            : ExogenousWorkflowFunction<'state,ScmModel> = workflow {
        let! state = getState ()
        do! iscmCommitForwardTracerMap ()
        do! SafetySharp.Workflow.updateState state.getModel
    }
    