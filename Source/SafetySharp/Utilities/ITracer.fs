﻿// The MIT License (MIT)
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

module internal ITracer =
    type ITracer<'traceableOfOrigin,'traceableOfState,'state> =
        interface
            abstract getTraceablesOfOrigin : 'traceableOfOrigin list
            abstract setTraceablesOfOrigin : 'traceableOfOrigin list -> 'state

            abstract getForwardTracer : ('traceableOfOrigin -> 'traceableOfState)
            abstract setForwardTracer : ('traceableOfOrigin -> 'traceableOfState) -> 'state
        end
    (*
    
    let initializeTracer<'state,'newTraceables>
            (traceables : 'newTraceables list)
                : WorkflowFunction<'state,'state,unit,'newTraceables,unit,'newTraceables,unit> =
        let behavior (wfState:WorkflowState<'state,unit,unit>) =
            let newWfState =
                {
                    WorkflowState.State = wfState.State;
                    WorkflowState.TraceablesOfOrigin = traceables;
                    WorkflowState.ForwardTracer = id;
                    WorkflowState.StepNumber = wfState.StepNumber;
                    WorkflowState.StepName = wfState.StepName;
                    WorkflowState.Log = wfState.Log;
                    WorkflowState.CancellationToken = wfState.CancellationToken;
                    WorkflowState.Tainted = wfState.Tainted; //tainted keeps old value, because state itself does not get changed!
                }
            (),newWfState            
        WorkflowFunction(behavior)
    
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
    let startNewTracer<'state,'traceableOfOrigin,'traceableOfState>
                : WorkflowFunction<'state,'state,'traceableOfOrigin,'traceableOfState,'traceableOfState,'traceableOfState,('traceableOfOrigin list)*('traceableOfOrigin->'traceableOfState)> =
        let behavior (wfState:WorkflowState<'state,'traceableOfOrigin,'traceableOfState>)
                : (('traceableOfOrigin list)*('traceableOfOrigin->'traceableOfState)) * (WorkflowState<'state,'traceableOfState,'traceableOfState>)  =
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

    let removeTraceables<'state,'traceableOfOrigin,'oldTraceableOfState> ()
                : WorkflowFunction<'state,'state,'traceableOfOrigin,'traceableOfOrigin,'oldTraceableOfState,unit,unit> =
        let behavior (wfState:WorkflowState<'state,'traceableOfOrigin,'oldTraceableOfState>) =
            let newWfState =
                {
                    WorkflowState.State = wfState.State;
                    WorkflowState.TraceablesOfOrigin = wfState.TraceablesOfOrigin;
                    WorkflowState.ForwardTracer =
                        let newTracer (toTrace:'traceableOfOrigin) : unit =
                            ()
                        newTracer;
                    WorkflowState.StepNumber = wfState.StepNumber;
                    WorkflowState.StepName = wfState.StepName;
                    WorkflowState.Log = wfState.Log;
                    WorkflowState.CancellationToken = wfState.CancellationToken;
                    WorkflowState.Tainted = wfState.Tainted; //tainted keeps old value, because state itself does not get changed!
                }
            (),newWfState            
        WorkflowFunction(behavior)

    let removeAllTraceables<'state,'traceableOfOrigin,'oldTraceableOfState> ()
                : WorkflowFunction<'state,'state,'traceableOfOrigin,unit,'oldTraceableOfState,unit,unit> =
        let behavior (wfState:WorkflowState<'state,'traceableOfOrigin,'oldTraceableOfState>) =
            let newWfState =
                {
                    WorkflowState.State = wfState.State;
                    WorkflowState.TraceablesOfOrigin = [];
                    WorkflowState.ForwardTracer = id
                    WorkflowState.StepNumber = wfState.StepNumber;
                    WorkflowState.StepName = wfState.StepName;
                    WorkflowState.Log = wfState.Log;
                    WorkflowState.CancellationToken = wfState.CancellationToken;
                    WorkflowState.Tainted = wfState.Tainted; //tainted keeps old value, because state itself does not get changed!
                }
            (),newWfState            
        WorkflowFunction(behavior)

    let getTraceablesOfOrigin<'state,'traceableOfOrigin,'traceableOfState> ()
                : EndogenousWorkflowFunction<'state,'traceableOfOrigin,'traceableOfState,'traceableOfOrigin list> =
        let behavior (wfState:WorkflowState<'state,'traceableOfOrigin,'oldTraceableOfState>) =
            (wfState.TraceablesOfOrigin),wfState
        WorkflowFunction(behavior)

    let getForwardTracer<'state,'traceableOfOrigin,'traceableOfState> ()
                : EndogenousWorkflowFunction<'state,'traceableOfOrigin,'traceableOfState,('traceableOfOrigin -> 'traceableOfState)> =
        let behavior (wfState:WorkflowState<'state,'traceableOfOrigin,'oldTraceableOfState>) =
            (wfState.ForwardTracer),wfState
        WorkflowFunction(behavior)
        
    let logForwardTracesOfOrigins<'state,'traceableOfOrigin,'traceableOfState> ()
                : EndogenousWorkflowFunction<'state,'traceableOfOrigin,'traceableOfState,unit> = workflow {
        let! traceablesOfOrigin = getTraceablesOfOrigin ()
        let! forwardTracer = getForwardTracer ()
        let tracedTraceables (traceable:'traceableOfOrigin) : string =
            let tracedTracable = forwardTracer traceable
            sprintf "trace %s to %s" (traceable.ToString()) (tracedTracable.ToString())
        let tracedTraceablesOfOrigin = traceablesOfOrigin |> List.map tracedTraceables
        do! listIter_seqState logEntry tracedTraceablesOfOrigin
    }
    *)

