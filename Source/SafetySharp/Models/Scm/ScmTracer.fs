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

module internal ScmMutable =
    open SafetySharp.Workflow
    open SafetySharp.ITracing
    open Scm
    open ScmHelpers
        
    type IScmMutable<'traceableOfOrigin,'state> =
        interface
            inherit ITracing<ScmModel,'traceableOfOrigin,Traceable,'state> 
            abstract setModel : ScmModel -> 'state
            
            abstract getUncommittedForwardTracerMap : Map<Traceable,Traceable> //to be able to inherit uncommitted traces
            abstract setUncommittedForwardTracerMap : Map<Traceable,Traceable> -> 'state //used to commit
        end

    type IScmMutableWorkflowFunction<'state,'traceableOfOrigin,'returnType when 'state :> IScmMutable<'traceableOfOrigin,'state>> =
        WorkflowFunction<'state,'state,'returnType>                

    let iscmGetModel<'traceableOfOrigin,'state when 'state :> IScmMutable<'traceableOfOrigin,'state>> () : IScmMutableWorkflowFunction<'state,'traceableOfOrigin,ScmModel> = workflow {
        let! iScmMutable = getState ()
        let model = iScmMutable.getModel
        return model
    }    
    
    let iscmSetModel<'traceableOfOrigin,'state when 'state :> IScmMutable<'traceableOfOrigin,'state>> (model:ScmModel) : IScmMutableWorkflowFunction<'state,'traceableOfOrigin,unit> = workflow {
        let! iScmMutable = getState ()
        let newIScmMutable = iScmMutable.setModel model
        do! updateState newIScmMutable
    }

    let iscmSetUncommittedForwardTracerMap<'traceableOfOrigin,'state when 'state :> IScmMutable<'traceableOfOrigin,'state>> (newUncommittedForwardTracerMap:Map<Traceable,Traceable>) : IScmMutableWorkflowFunction<'state,'traceableOfOrigin,unit> = workflow {
        let! iScmMutable = getState ()
        let newIScmMutable = iScmMutable.setUncommittedForwardTracerMap newUncommittedForwardTracerMap
        do! updateState newIScmMutable
    }    

    let iscmGetUncommittedForwardTracerMap<'traceableOfOrigin,'state when 'state :> IScmMutable<'traceableOfOrigin,'state>> () : IScmMutableWorkflowFunction<'state,'traceableOfOrigin,Map<Traceable,Traceable>> = workflow {
        let! iScmMutable = getState ()
        let uncommittedForwardTracerMap = iScmMutable.getUncommittedForwardTracerMap
        return uncommittedForwardTracerMap
    } 

    let iscmGetTraceablesOfOrigin<'traceableOfOrigin,'state when 'state :> IScmMutable<'traceableOfOrigin,'state>> () : IScmMutableWorkflowFunction<'state,'traceableOfOrigin,'traceableOfOrigin list> = workflow {
        let! iScmMutable = getState ()
        let traceablesOfOrigin = iScmMutable.getTraceablesOfOrigin
        return traceablesOfOrigin
    } 

    let iscmGetForwardTracer<'traceableOfOrigin,'state when 'state :> IScmMutable<'traceableOfOrigin,'state>> () : IScmMutableWorkflowFunction<'state,'traceableOfOrigin,('traceableOfOrigin -> Traceable)> = workflow {
        let! iScmMutable = getState ()
        let forwardTracer = iScmMutable.getForwardTracer
        return forwardTracer
    } 
    
    let iscmTraceTraceable<'traceableOfOrigin,'state when 'state :> IScmMutable<'traceableOfOrigin,'state>> (_from:Traceable) (_to:Traceable) : IScmMutableWorkflowFunction<'state,'traceableOfOrigin,unit> = workflow {
        let! uncommittedForwardTracerMap = iscmGetUncommittedForwardTracerMap ()
        let newUncommittedForwardTracerMap =
            if uncommittedForwardTracerMap.ContainsKey _from then
                failwith "BUG: There exists already an entry for this traceable. The traceable is not unique. Maybe because there was a name clash."
            uncommittedForwardTracerMap.Add(_from,_to)
        do! iscmSetUncommittedForwardTracerMap newUncommittedForwardTracerMap
    }    

    let iscmCommitForwardTracerMap<'traceableOfOrigin,'state when 'state :> IScmMutable<'traceableOfOrigin,'state>> () : IScmMutableWorkflowFunction<'state,'traceableOfOrigin,unit> = workflow {
        let! iScmMutable = getState ()

        let forwardTracerMapInClosure = iScmMutable.getUncommittedForwardTracerMap
        let newForwardTracer (originValue:'traceableOfOrigin) =
            let oldValue = iScmMutable.getForwardTracer (originValue)
            let rec findValue (oldValue:Traceable) =
                if forwardTracerMapInClosure.ContainsKey oldValue then
                    findValue (forwardTracerMapInClosure.Item oldValue)
                else
                    oldValue
            findValue oldValue
        
        let emptyUncommittedTracerMap = Map.empty<Traceable,Traceable>
        let newIScmMutable = iScmMutable.setUncommittedForwardTracerMap emptyUncommittedTracerMap
        let newIScmMutable = newIScmMutable.setForwardTracer newForwardTracer
        do! updateState newIScmMutable
    }
    
    let scmGetModel () : WorkflowFunction<Scm.ScmModel,Scm.ScmModel,Scm.ScmModel> = workflow {
        let! model = getState ()
        return model
    }

    let scmSetModel<'oldIrrelevantState> (model:ScmModel)
            : ExogenousWorkflowFunction<'oldIrrelevantState,Scm.ScmModel> = workflow {
        do! updateState model
    }

    type SimpleScmMutable<'traceableOfOrigin> = {
            Model:ScmModel;
            UncommitedForwardTracerMap:Map<Traceable,Traceable>;
            TraceablesOfOrigin : 'traceableOfOrigin list;
            ForwardTracer : 'traceableOfOrigin -> Traceable;
        }
            with

                member this.getModel : ScmModel = this.Model
                interface IScmMutable<'traceableOfOrigin,SimpleScmMutable<'traceableOfOrigin>> with
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

    
    type SimpleScmMutableWorkflowFunction<'traceableOfOrigin,'returnType> =
        WorkflowFunction<SimpleScmMutable<'traceableOfOrigin>,SimpleScmMutable<'traceableOfOrigin>,'returnType>
        
       
    let setInitialPlainModelState<'oldIrrelevantState> (model:ScmModel)
            : WorkflowFunction<'oldIrrelevantState,SimpleScmMutable<Traceable>,unit> = workflow {
        let emptyUncommittedTracerMap = Map.empty<Traceable,Traceable>
        let scmMutable =
            {
                SimpleScmMutable.Model = model;
                SimpleScmMutable.UncommitedForwardTracerMap = emptyUncommittedTracerMap;
                SimpleScmMutable.TraceablesOfOrigin = model.getTraceables;
                SimpleScmMutable.ForwardTracer = id;
            }
        do! updateState scmMutable
    }
        
    let iscmToPlainModelState<'state,'traceableOfOrigin when 'state :> IScmMutable<'traceableOfOrigin,'state>> ()
            : ExogenousWorkflowFunction<'state,SimpleScmMutable<'traceableOfOrigin>> = workflow {
        let! state = getState ()
        let scmMutable =
            {
                SimpleScmMutable.Model = state.getModel;
                SimpleScmMutable.UncommitedForwardTracerMap = state.getUncommittedForwardTracerMap;  //inherit uncommitted traces
                SimpleScmMutable.TraceablesOfOrigin = state.getTraceablesOfOrigin;
                SimpleScmMutable.ForwardTracer = state.getForwardTracer;
            }
        do! updateState scmMutable
    }
        
    let iscmToScmState<'state,'traceableOfOrigin when 'state :> IScmMutable<'traceableOfOrigin,'state>> ()
            : ExogenousWorkflowFunction<'state,ScmModel> = workflow {
        let! state = getState ()
        do! iscmCommitForwardTracerMap ()
        do! SafetySharp.Workflow.updateState state.getModel
    }
    