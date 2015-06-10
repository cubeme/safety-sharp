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

namespace SafetySharp

module internal ITracing =
    type ITracing<'model,'traceableOfOrigin,'traceableOfModel,'state> =
        interface
            abstract getModel : 'model

            abstract getTraceables : 'traceableOfModel list

            abstract getTraceablesOfOrigin : 'traceableOfOrigin list
            abstract setTraceablesOfOrigin : 'traceableOfOrigin list -> 'state

            abstract getForwardTracer : ('traceableOfOrigin -> 'traceableOfModel)
            abstract setForwardTracer : ('traceableOfOrigin -> 'traceableOfModel) -> 'state
        end
        
    open SafetySharp.Workflow

    let getTraceablesOfOrigin<'model,'state,'traceableOfOrigin,'traceableOfModel when 'state :> ITracing<'model,'traceableOfOrigin,'traceableOfModel,'state> > ()
                : WorkflowFunction<'state,'state,'traceableOfOrigin list> =
        let behavior (wfState:WorkflowState<'state>) =
            (wfState.State.getTraceablesOfOrigin),wfState
        WorkflowFunction(behavior)

    let getForwardTracer<'model,'state,'traceableOfOrigin,'traceableOfModel when 'state :> ITracing<'model,'traceableOfOrigin,'traceableOfModel,'state> > ()
                : WorkflowFunction<'state,'state,('traceableOfOrigin -> 'traceableOfModel)> =
        let behavior (wfState:WorkflowState<'state>) =
            (wfState.State.getForwardTracer),wfState
        WorkflowFunction(behavior)
        
    let logForwardTracesOfOrigins<'model,'state,'traceableOfOrigin,'traceableOfModel when 'state :> ITracing<'model,'traceableOfOrigin,'traceableOfModel,'state> > ()
                : WorkflowFunction<'state,'state,unit> = workflow {
        let! traceablesOfOrigin = getTraceablesOfOrigin ()
        let! forwardTracer = getForwardTracer ()
        let tracedTraceables (traceable:'traceableOfOrigin) : string =
            let tracedTracable = forwardTracer traceable
            sprintf "trace %s to %s" (traceable.ToString()) (tracedTracable.ToString())
        let tracedTraceablesOfOrigin = traceablesOfOrigin |> List.map tracedTraceables
        do! listIter_seqState logEntry tracedTraceablesOfOrigin
    }

    let removeTracing<'model,'state,'traceableOfOrigin,'traceableOfModel when 'state :> ITracing<'model,'traceableOfOrigin,'traceableOfModel,'state> > ()
                : WorkflowFunction<'state,'model,unit> = workflow {
        let! state = getState ()
        do! updateState (state.getModel)
    }

    (*
    
    let updateTracer<'state,'traceableOfOrigin,'oldTraceableOfState,'newTraceableOfState>
            (intermediateForwardTracer : 'oldTraceableOfState -> 'newTraceableOfState)
                : WorkflowFunction<'state,'state,'traceableOfOrigin,'traceableOfOrigin,'oldTraceableOfState,'newTraceableOfState,unit> =
        let behavior (wfState:WorkflowState<'state,'traceableOfOrigin,'oldTraceableOfState>) =
            let newWfState =
                {
                    WorkflowState.State = wfState.State;
                    WorkflowState.TraceablesOfOrigin = wfState.TraceablesOfOrigin;
                    WorkflowState.ForwardTracer =
                        let newTracer (toTrace:'traceableOfOrigin) =
                            let toOldTraceEnd = wfState.ForwardTracer toTrace
                            intermediateForwardTracer toOldTraceEnd
                        newTracer;
                    WorkflowState.StepNumber = wfState.StepNumber;
                    WorkflowState.StepName = wfState.StepName;
                    WorkflowState.Log = wfState.Log;
                    WorkflowState.CancellationToken = wfState.CancellationToken;
                    WorkflowState.Tainted = wfState.Tainted; //tainted keeps old value, because state itself does not get changed!
                }
            (),newWfState            
        WorkflowFunction(behavior)
                
    // returns old traceables of the origin and tracer
    let startNewTracer<'state,'traceableOfOrigin,'traceableOfModel>
                : WorkflowFunction<'state,'state,'traceableOfOrigin,'traceableOfModel,'traceableOfModel,'traceableOfModel,('traceableOfOrigin list)*('traceableOfOrigin->'traceableOfModel)> =
        let behavior (wfState:WorkflowState<'state,'traceableOfOrigin,'traceableOfModel>)
                : (('traceableOfOrigin list)*('traceableOfOrigin->'traceableOfModel)) * (WorkflowState<'state,'traceableOfModel,'traceableOfModel>)  =
            let newWfState =
                {
                    WorkflowState.State = wfState.State;
                    WorkflowState.TraceablesOfOrigin =
                        wfState.TraceablesOfOrigin |> List.map (wfState.ForwardTracer); //trace every original traceable
                    WorkflowState.ForwardTracer = id
                    WorkflowState.StepNumber = wfState.StepNumber;
                    WorkflowState.StepName = wfState.StepName;
                    WorkflowState.Log = wfState.Log;
                    WorkflowState.CancellationToken = wfState.CancellationToken;
                    WorkflowState.Tainted = wfState.Tainted; //tainted keeps old value, because state itself does not get changed!
                }
            (wfState.TraceablesOfOrigin,wfState.ForwardTracer),newWfState
        WorkflowFunction(behavior)

    *)

