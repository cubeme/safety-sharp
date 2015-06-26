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

module internal Workflow =

    // Note on compiler error "Value restriction":
    //    http://blogs.msdn.com/b/mulambda/archive/2010/05/01/value-restriction-in-f.aspx
    //    The solution we use is to make everything a function. Empty parameter is added, if otherwise no parameter.
    

    type WorkflowState<'state> = {
        State : 'state;
        StepNumber : int list;
        StepName : string list;
        Log : string list;
        LogEvent : Event<string>;
        EngineOptions : Map<string,SafetySharp.EngineOptions.IEngineOption>;
        CancellationToken : System.Threading.CancellationToken option; //https://msdn.microsoft.com/de-de/library/dd997364(v=vs.110).aspx
        Tainted : bool; // Use tainted to indicate, if a function changed something. Do not compare states, because now it is obvious, what happens, when a mutable changes. TODO: move to iscmTracer/IIterateableWorkflow, because the use here changed.
        // GeneratedFilesAndDirs
    }

    type WorkflowState with
        member this.CurrentStepNumber = this.StepNumber.Head
        member this.CurrentStepName = this.StepName.Head
    
    
    let workflowState_emptyInit () : WorkflowState<unit> =
        {
            WorkflowState.State = ();
            WorkflowState.StepNumber = [];
            WorkflowState.StepName = [];
            WorkflowState.Log = [];
            WorkflowState.LogEvent = new Event<string>();
            WorkflowState.EngineOptions = Map.empty<string,SafetySharp.EngineOptions.IEngineOption>;
            WorkflowState.CancellationToken = None;
            WorkflowState.Tainted = false;
        }
    let workflowState_stateInit<'state> (state:'state) : WorkflowState<'state> =
        {
            WorkflowState.State = state;
            WorkflowState.StepNumber = [];
            WorkflowState.StepName = [];
            WorkflowState.Log = [];
            WorkflowState.LogEvent = new Event<string>();
            WorkflowState.EngineOptions = Map.empty<string,SafetySharp.EngineOptions.IEngineOption>;
            WorkflowState.CancellationToken = None;
            WorkflowState.Tainted = false;
        }


    
    // WorkflowFunction is the main and most generic primitive of the workflow computation expression
    type WorkflowFunction<'oldState,'newState,'returnType> =
        WorkflowFunction of (WorkflowState<'oldState> -> 'returnType * WorkflowState<'newState>)        
    
    // Convenience: Type abbreviations for WorkflowFunction. They also allow using "_" as placeholder in type annotations.


    // InitialWorkflowFunction:
    //    These workflow functions have an empty state as 'oldState.
    type InitialWorkflowFunction<'newState,'returnType> =
        WorkflowFunction<unit,'newState,'returnType>
                
    // EndogenousWorkflowFunction:
    //    These workflow functions keep the type of the state
    //    A EndogenousWorkflowFunction may be used to implement a M2M-transformation when the type of the model does not change (endogenous transformation).
    type EndogenousWorkflowFunction<'state> =
        WorkflowFunction<'state,'state,unit>

    // ExogenousWorkflowFunction:
    //    These workflow functions modify the type of state
    //    A ExogenousWorkflowFunction may be used to implement a M2M-transformation when the type of the model changes (exogenous transformation).
    type ExogenousWorkflowFunction<'oldState,'newState> =
        WorkflowFunction<'oldState,'newState,unit>

    let runWorkflowState (WorkflowFunction s) a = s a
    let getWorkflowState () = WorkflowFunction (fun s -> (s,s)) //Called in workflow: (implicitly) gets wfState (s) from workflow; assign this State s to the let!; and set (in this case keep) wfState to s
    let getState () = WorkflowFunction (fun s -> (s.State,s)) // gets the inner state
    let putWorkflowState s = WorkflowFunction (fun _ -> ((),s)) //Called in workflow: ignore state (_) from workflow; assign nothing () to the let!; and set wfState to the new wfState s
    let putWorkflowStateAndReturn s returnValue = WorkflowFunction (fun _ -> (returnValue,s))//Called in workflow: ignore wfState (_); assign returnValue to the let!; and set wfState to the new wfState s
    

    /////////////////////////// Execution of SubWorkflows ///////////////////////////////
    // runSubWorkflow restores the old state    


    let runSubWorkflow_WithState_ReturnState<'mainState,'subStateStart,'subStateFinal,'returnType>
                        (s:WorkflowFunction<'subStateStart,'subStateFinal,'returnType>)
                        (subStateStart:'subStateStart)
                    : WorkflowFunction<'mainState,'mainState,'subStateFinal> =
        let behavior (wfState:WorkflowState<'mainState>) =
            let subWfStateStart =
                {
                    WorkflowState.State = subStateStart;
                    WorkflowState.StepNumber = wfState.StepNumber;
                    WorkflowState.StepName = wfState.StepName;
                    WorkflowState.Log = wfState.Log;
                    WorkflowState.LogEvent = wfState.LogEvent;
                    WorkflowState.EngineOptions = wfState.EngineOptions;
                    WorkflowState.CancellationToken = wfState.CancellationToken;
                    WorkflowState.Tainted = wfState.Tainted;
                }
            let functionToExecute = match s with | WorkflowFunction(s)->s
            let subResult,subWfStateFinal = functionToExecute subWfStateStart
            let newWfState =
                {
                    WorkflowState.State = wfState.State; // restore old State
                    WorkflowState.StepNumber = subWfStateFinal.StepNumber;
                    WorkflowState.StepName = subWfStateFinal.StepName;
                    WorkflowState.Log = subWfStateFinal.Log;
                    WorkflowState.LogEvent = subWfStateFinal.LogEvent;
                    WorkflowState.EngineOptions = subWfStateFinal.EngineOptions;
                    WorkflowState.CancellationToken = subWfStateFinal.CancellationToken;
                    WorkflowState.Tainted = wfState.Tainted; // restore old Tainted
                }
            subWfStateFinal.State,newWfState
        WorkflowFunction(behavior)
        
    let runSubWorkflow_WithState_ReturnResult<'mainState,'subStateStart,'subStateFinal,'returnType>
                        (s:WorkflowFunction<'subStateStart,'subStateFinal,'returnType>)
                        (subStateStart:'subStateStart)
                    : WorkflowFunction<'mainState,'mainState,'returnType> =
        let behavior (wfState:WorkflowState<'mainState>) =
            let subWfStateStart =
                {
                    WorkflowState.State = subStateStart;
                    WorkflowState.StepNumber = wfState.StepNumber;
                    WorkflowState.StepName = wfState.StepName;
                    WorkflowState.Log = wfState.Log;
                    WorkflowState.LogEvent = wfState.LogEvent;
                    WorkflowState.EngineOptions = wfState.EngineOptions;
                    WorkflowState.CancellationToken = wfState.CancellationToken;
                    WorkflowState.Tainted = wfState.Tainted;
                }
            let functionToExecute = match s with | WorkflowFunction(s)->s
            let subResult,subWfStateFinal = functionToExecute subWfStateStart
            let newWfState =
                {
                    WorkflowState.State = wfState.State; // restore old State
                    WorkflowState.StepNumber = subWfStateFinal.StepNumber;
                    WorkflowState.StepName = subWfStateFinal.StepName;
                    WorkflowState.Log = subWfStateFinal.Log;
                    WorkflowState.LogEvent = subWfStateFinal.LogEvent;
                    WorkflowState.EngineOptions = subWfStateFinal.EngineOptions;
                    WorkflowState.CancellationToken = subWfStateFinal.CancellationToken;
                    WorkflowState.Tainted = wfState.Tainted; // restore old Tainted
                }
            subResult,newWfState
        WorkflowFunction(behavior)
        
    let runSubWorkflow_WithEmptyState_ReturnState s = runSubWorkflow_WithState_ReturnState s ()

    let runSubWorkflow_WithEmptyState_ReturnResult s = runSubWorkflow_WithState_ReturnResult s ()

    
    let runSubWorkflow_WithSameState_ReturnState<'state,'subStateFinal,'returnType>
                        (s:WorkflowFunction<'state,'subStateFinal,'returnType>)
                    : WorkflowFunction<'state,'state,'subStateFinal> =
        let behavior (wfState:WorkflowState<'state>) =
            let functionToExecute = match s with | WorkflowFunction(s)->s
            let subResult,subWfStateFinal = functionToExecute wfState
            let newWfState =
                {
                    WorkflowState.State = wfState.State; // restore old State
                    WorkflowState.StepNumber = subWfStateFinal.StepNumber;
                    WorkflowState.StepName = subWfStateFinal.StepName;
                    WorkflowState.Log = subWfStateFinal.Log;
                    WorkflowState.LogEvent = subWfStateFinal.LogEvent;
                    WorkflowState.EngineOptions = subWfStateFinal.EngineOptions;
                    WorkflowState.CancellationToken = subWfStateFinal.CancellationToken;
                    WorkflowState.Tainted = wfState.Tainted; // restore old Tainted
                }
            subWfStateFinal.State,newWfState
        WorkflowFunction(behavior)
        
    let runSubWorkflow_WithSameState_ReturnResult<'state,'subStateFinal,'returnType>
                        (s:WorkflowFunction<'state,'subStateFinal,'returnType>)
                    : WorkflowFunction<'state,'state,'returnType> =
        let behavior (wfState:WorkflowState<'state>) =
            let functionToExecute = match s with | WorkflowFunction(s)->s
            let subResult,subWfStateFinal = functionToExecute wfState
            let newWfState =
                {
                    WorkflowState.State = wfState.State; // restore old State
                    WorkflowState.StepNumber = subWfStateFinal.StepNumber;
                    WorkflowState.StepName = subWfStateFinal.StepName;
                    WorkflowState.Log = subWfStateFinal.Log;
                    WorkflowState.LogEvent = subWfStateFinal.LogEvent;
                    WorkflowState.EngineOptions = subWfStateFinal.EngineOptions;
                    WorkflowState.CancellationToken = subWfStateFinal.CancellationToken;
                    WorkflowState.Tainted = wfState.Tainted; // restore old Tainted
                }
            subResult,newWfState
        WorkflowFunction(behavior)
        
    /////////////////////////// Common Workflow functions ///////////////////////////////

    let updateState<'oldState,'newState>
            (newState:'newState)
                : ExogenousWorkflowFunction<'oldState,'newState> =
        let behavior (wfState:WorkflowState<'oldState>) =
            let newWfState =
                {
                    WorkflowState.State = newState;
                    WorkflowState.StepNumber = wfState.StepNumber;
                    WorkflowState.StepName = wfState.StepName;
                    WorkflowState.Log = wfState.Log;
                    WorkflowState.LogEvent = wfState.LogEvent;
                    WorkflowState.EngineOptions = wfState.EngineOptions;
                    WorkflowState.CancellationToken = wfState.CancellationToken;
                    WorkflowState.Tainted = true;
                }
            (),newWfState
        WorkflowFunction(behavior)

                        
    let logEntry<'state> (entry:string) : EndogenousWorkflowFunction<'state> =
        let behavior (wfState:WorkflowState<'state>) =
            do printfn "%s" entry
            do wfState.LogEvent.Trigger entry
            let newWfState =
                { wfState with
                    WorkflowState.Log = entry :: wfState.Log;
                    // WorkflowState.Tainted = wfState.Tainted; //tainted keeps old value, because state itself does not get changed!
                }
            (),newWfState
        WorkflowFunction(behavior)
        
    let setEngineOption<'state,'engineOption when 'engineOption :> SafetySharp.EngineOptions.IEngineOption> (engineOption:'engineOption) : EndogenousWorkflowFunction<'state> =
        let behavior (wfState:WorkflowState<'state>) =
            let nameOfEngineOptionAsString =
                let typeOfEngineOption = typeof<'engineOption>
                typeOfEngineOption.AssemblyQualifiedName
            let newWfState =
                { wfState with
                    WorkflowState.EngineOptions = wfState.EngineOptions.Add(nameOfEngineOptionAsString,engineOption);
                    // WorkflowState.Tainted = wfState.Tainted; //tainted keeps old value, because state itself does not get changed!
                }
            (),newWfState
        WorkflowFunction(behavior)
        
        
    let setIEngineOption<'state> (engineOption:SafetySharp.EngineOptions.IEngineOption) : EndogenousWorkflowFunction<'state> =
        let behavior (wfState:WorkflowState<'state>) =
            let nameOfEngineOptionAsString =
                let typeOfEngineOption = engineOption.GetType() // returns the exact type, not only the interface. Is resolved on runtime
                typeOfEngineOption.AssemblyQualifiedName
            let newWfState =
                { wfState with
                    WorkflowState.EngineOptions = wfState.EngineOptions.Add(nameOfEngineOptionAsString,engineOption);
                    // WorkflowState.Tainted = wfState.Tainted; //tainted keeps old value, because state itself does not get changed!
                }
            (),newWfState
        WorkflowFunction(behavior)
        
    let getEngineOption<'state,'engineOption when 'engineOption :> SafetySharp.EngineOptions.IEngineOption> () : WorkflowFunction<'state,'state,'engineOption> =
        let behavior (wfState:WorkflowState<'state>) =
            let nameOfEngineOptionAsString = SafetySharp.EngineOptions.EngineOptionHelpers.nameOfEngineOptionAsString<'engineOption> ()
            let result =
                if wfState.EngineOptions.ContainsKey nameOfEngineOptionAsString then
                    (wfState.EngineOptions.Item nameOfEngineOptionAsString) :?> 'engineOption
                else
                    (EngineOptions.DefaultEngineOptions.DefaultEngineOptions.Item nameOfEngineOptionAsString) :?> 'engineOption
            (result),wfState
        WorkflowFunction(behavior)
        
    let isEngineOption<'state,'engineOption when 'engineOption :> SafetySharp.EngineOptions.IEngineOption> (engineOption:'engineOption) : WorkflowFunction<'state,'state,bool> =
        let behavior (wfState:WorkflowState<'state>) =
            let nameOfEngineOptionAsString =
                let typeOfEngineOption = typeof<'engineOption>
                typeOfEngineOption.AssemblyQualifiedName
            let engineOption = engineOption :> SafetySharp.EngineOptions.IEngineOption
            let currentEngineOption =
                if wfState.EngineOptions.ContainsKey nameOfEngineOptionAsString then
                    (wfState.EngineOptions.Item nameOfEngineOptionAsString)
                else
                    (EngineOptions.DefaultEngineOptions.DefaultEngineOptions.Item nameOfEngineOptionAsString)
            let result = (engineOption=currentEngineOption)
            (result),wfState
        WorkflowFunction(behavior)

    let trackSteps_NextStep<'state> (stepName:string) : EndogenousWorkflowFunction<'state> = 
        let behavior (wfState:WorkflowState<'state>) =
            let newWfState =
                if wfState.StepNumber = [] then
                    { wfState with
                        WorkflowState.StepName = [stepName] ;
                        WorkflowState.StepNumber = [1] ;
                        // WorkflowState.Tainted = wfState.Tainted; //tainted keeps old value, because state itself does not get changed!
                    }
                else
                    let previousStep = wfState.StepNumber.Head
                    { wfState with
                        WorkflowState.StepName = stepName :: wfState.StepName.Tail ;
                        WorkflowState.StepNumber = (previousStep+1) :: wfState.StepNumber.Tail;
                        // WorkflowState.Tainted = wfState.Tainted; //tainted keeps old value, because state itself does not get changed!
                    }
            let newStepNumberString = newWfState.StepNumber |> List.rev |> List.map string |> String.concat "."
            let newEntry = sprintf "Entering step %s '%s'" newStepNumberString stepName
            do printfn "%s" newEntry
            (),newWfState            
        WorkflowFunction(behavior)
                
    let trackSteps_CreateSubstepAndEnter<'state> (stepName:string) : EndogenousWorkflowFunction<'state> = 
        let behavior (wfState:WorkflowState<'state>) =
            let newWfState =
                { wfState with
                    WorkflowState.StepNumber = 1 :: wfState.StepNumber; //begin with step 1
                    WorkflowState.StepName = stepName :: wfState.StepName ;
                    // WorkflowState.Tainted = wfState.Tainted; //tainted keeps old value, because state itself does not get changed!
                }
            let newStepNumberString = newWfState.StepNumber |> List.rev |> List.map string |> String.concat "."
            let newEntry = sprintf "Entering step %s '%s'" newStepNumberString stepName
            do printfn "%s" newEntry
            (),newWfState
        WorkflowFunction(behavior)

    let trackSteps_LeaveSubstep<'state> () : EndogenousWorkflowFunction<'state> = 
        let behavior (wfState:WorkflowState<'state>) =
            let newWfState =
                { wfState with
                    WorkflowState.StepName = wfState.StepName.Tail ;
                    WorkflowState.StepNumber = wfState.StepNumber.Tail;
                    // WorkflowState.Tainted = wfState.Tainted; //tainted keeps old value, because state itself does not get changed!
                }
            (),newWfState            
        WorkflowFunction(behavior)


    let iterateToFixpoint<'state,'traceableOfOrigin> ( (WorkflowFunction(functionToIterate)) : EndogenousWorkflowFunction<'state>) : EndogenousWorkflowFunction<'state> =
        let adjust_tainted_and_call (wfState:WorkflowState<'state>) : (bool*WorkflowState<'state>) =
            // 1) Tainted is set to false
            // 2) function is called
            // 3) Tainted is set to true, if (at least one option applies)
            //      a) it was true before the function call
            //      b) the functionToIterate sets tainted to true 
            let wasTaintedBefore = wfState.Tainted
            let stateButUntainted =
                { wfState with
                    WorkflowState.Tainted = false;
                }
            let (returnValue:unit,wfStateAfterCall) = functionToIterate stateButUntainted
            let taintedByCall = wfStateAfterCall.Tainted
            let newWfState =
                { wfStateAfterCall with
                    WorkflowState.Tainted = wasTaintedBefore || taintedByCall;
                }
            (taintedByCall,newWfState)
        let rec iterate (wfState:WorkflowState<'state>) : (unit*WorkflowState<'state>) =
            let (taintedByCall,wfStateAfterOneCall) = adjust_tainted_and_call wfState
            if taintedByCall then
                iterate wfStateAfterOneCall
            else
                ((),wfStateAfterOneCall)
        WorkflowFunction (iterate)

    // Allows the use of a workflow function on a list. Result is the same as execution the function sequentially on each element.
    let listIter_seqState<'state,'inputListType>
                (workflowFunctionWithParameter : 'inputListType -> EndogenousWorkflowFunction<'state>)
                (listToIterate:'inputListType list)
                    : EndogenousWorkflowFunction<'state> =        
        let behavior (wfState:WorkflowState<'state>) : (unit*WorkflowState<'state>) =
            let rec iterate (intermediateWfState:WorkflowState<'state>) (listToIterate:'inputListType list) =
                if listToIterate.IsEmpty then
                    ((),intermediateWfState)
                else
                    let element = listToIterate.Head
                    let functionToIterate = match workflowFunctionWithParameter element with | WorkflowFunction(functionToIterate) -> functionToIterate
                    let (_,newIntermediateWfState) = functionToIterate intermediateWfState
                    iterate newIntermediateWfState listToIterate.Tail
            iterate wfState listToIterate
        WorkflowFunction (behavior)

        
    // Allows the use of a workflow function on a list with an accumulator. Result is the same as execution the function sequentially on each element.
    // Example:
    //     let executeStatementsWf (acc:PreviousResult) (stmnts:Statement list) : WorkflowFunction<ExecutionState,ExecutionState,ExecutionResult> = ...
    //     let! result : ExecutionResult = listFold executeStatementsWf PreviousResult.Good stmnts
    let listFold<'state,'inputListType,'acc>
                (workflowFunctionWithParameter : 'acc -> 'inputListType -> WorkflowFunction<'state,'state,'acc>)
                (initialAcc:'acc)
                (listToIterate:'inputListType list)
                    : WorkflowFunction<'state,'state,'acc> =        
        let behavior (wfState:WorkflowState<'state>) : ('acc*WorkflowState<'state>) =
            let rec fold (intermediateWfState:WorkflowState<'state>) (intermediateAcc:'acc) (listToIterate:'inputListType list) =
                if listToIterate.IsEmpty then
                    (intermediateAcc,intermediateWfState)
                else
                    let element = listToIterate.Head
                    let functionToFold = match workflowFunctionWithParameter intermediateAcc element with | WorkflowFunction(functionToFold) -> functionToFold
                    let (newAcc,newIntermediateWfState) = functionToFold intermediateWfState
                    fold newIntermediateWfState newAcc listToIterate.Tail
            fold wfState initialAcc listToIterate
        WorkflowFunction (behavior)
                
    // Allows the use of a workflow function on a list with a collection of the results. State is the same as executing the workflow on each
    // element in sequence (original state is not preserved)
    // Example 1:
    //     let returnPlusOneWf (value:int) : WorkflowFunction<ExecutionState,ExecutionState,int> = ...
    //     let! result : int list = listMap returnPlusOneWf elements
    // Example 2:
    //     let returnPlusOneWf (value:int) : WorkflowFunction<ExecutionState,int,unit> = ...
    //     let returnPlusOneWf_asSubWorkflow element = runSubWorkflow_WithSameState_ReturnState (returnPlusOneWf element)
    //     let! result : int list = listMap returnPlusOneWf_asSubWorkflow elements
    // Example 3:
    //     let returnPlusOneWf (value:int) : WorkflowFunction<ExecutionState,ExecutionState,int> = ...
    //     let returnPlusOneWf_asSubWorkflow element = runSubWorkflow_WithSameState_ReturnResult (returnPlusOneWf element)
    //     let! result : int list = listMap returnPlusOneWf_asSubWorkflow elements
    let listMap<'state,'inputType,'resultType>
                (workflowFunctionWithParameter : 'inputType -> WorkflowFunction<'state,'state,'resultType>)
                (listToIterate:'inputType list)
                    : WorkflowFunction<'state,'state,'resultType list> =
        let behavior (wfState:WorkflowState<'state>) : ('resultType list * WorkflowState<'state>) =
            let rec mapNext (intermediateWfState:WorkflowState<'state>) (alreadyMapped:'resultType list) (listToIterate:'inputType list) =
                if listToIterate.IsEmpty then
                    (alreadyMapped |> List.rev,intermediateWfState)
                else
                    let element = listToIterate.Head
                    let functionToMap = match workflowFunctionWithParameter element with | WorkflowFunction(functionToMap) -> functionToMap
                    let (newElement,newIntermediateWfState) = functionToMap intermediateWfState
                    mapNext newIntermediateWfState (newElement::alreadyMapped) listToIterate.Tail
            mapNext wfState [] listToIterate
        WorkflowFunction (behavior)

    (* TODO            
    // Allows the use of a workflow function on a list. Result is the same as execution each function on the source state. Source state is preserved.
    // Can be used for "what if" analysis, where different checks are started and evaluated from the same source state. Executed independently.
    let listIter_srcState = ()
    
    // Allows the use of a workflow function on a list. Result is the same as execution each function on the source state. Source state is preserved.
    // Can be used for "what if" analysis, where different checks are started and evaluated from the same source state and collecting the results.
    // Executed independently.
    let listMap_srcState = ()
    *)

    let runWorkflow_getResultAndWfState<'newState,'returnType>
                (WorkflowFunction s:(WorkflowFunction<unit,'newState,'returnType>)) =
        // no cancellation token
        let result,newWfState = s (workflowState_emptyInit ())
        (result,newWfState)
                              
    let runWorkflow_getResult<'newState,'returnType>
                (WorkflowFunction s:(WorkflowFunction<unit,'newState,'returnType>)) =
        // no cancellation token
        let result,newWfState = s (workflowState_emptyInit ())
        result
        
    let runWorkflow_getState<'newState,'returnType>
                (WorkflowFunction s:(WorkflowFunction<unit,'newState,'returnType>)) =
        // no cancellation token
        let result,newWfState = s (workflowState_emptyInit ())
        newWfState.State
          
    let runWorkflow_getWfState<'newState,'returnType>
                (WorkflowFunction s:(WorkflowFunction<unit,'newState,'returnType>)) =
        // no cancellation token
        let result,newWfState = s (workflowState_emptyInit ())
        newWfState
          
    let runWorkflowState_getState<'oldState,'newState,'returnType>
                    (WorkflowFunction s:(WorkflowFunction<'oldState,'newState,'returnType>))
                    (initialState:WorkflowState<'oldState>) 
                        : 'newState =
        let result,newWfState = s (initialState)
        newWfState.State
        
    let runWorkflowState_getWfState<'oldState,'newState,'returnType>
                    (WorkflowFunction s:(WorkflowFunction<'oldState,'newState,'returnType>))
                    (initialState:WorkflowState<'oldState>) 
                        : WorkflowState<'newState> =
        let result,newWfState = s (initialState)
        newWfState
          
    let runWorkflowState_getResult<'oldState,'newState,'returnType>
                    (WorkflowFunction s:(WorkflowFunction<'oldState,'newState,'returnType>))
                    (initialState:WorkflowState<'oldState>) 
                        : 'returnType =
        let result,newWfState = s (initialState)
        result
        
    let ignoreResult<'oldState,'newState,'oldTraceableOfOrigin,'newTraceableOfOrigin,'oldTraceableOfState,'newTraceableOfState,'returnType>
                    (WorkflowFunction s:(WorkflowFunction<'oldState,'newState,'returnType>))
                        : WorkflowFunction<'oldState,'newState,unit> =
        let ignoreResult oldState =
            let result,newState = s oldState
            (),newState
        WorkflowFunction (ignoreResult)

    type Workflow() =
        member this.Return(a) = 
            WorkflowFunction (fun s -> (a,s))
        member this.Bind(m,k) =
            WorkflowFunction (fun wfState -> 
                let (a,wfState') = runWorkflowState m wfState
                if wfState'.CancellationToken.IsSome && wfState'.CancellationToken.Value.IsCancellationRequested then //short-circuit
                    // TODO: Add log entry
                    // Was canceled. Do not execute next command in pipeline
                    raise (System.OperationCanceledException(wfState'.CancellationToken.Value))
                else
                    runWorkflowState (k a) wfState')
        member this.ReturnFrom (m) =
            m
        member this.Zero<'oldState> () =
            let behavior (wfState:WorkflowState<'oldState>) =
                (),wfState
            WorkflowFunction(behavior)
            

    let workflow = new Workflow()
    
    ////////////// Basic Workflow element
    let readFile<'oldIrrelevantState>
            (inputFile:string)
                : ExogenousWorkflowFunction<'oldIrrelevantState,string> = workflow {
        let input = System.IO.File.ReadAllText inputFile
        do! updateState input
    }
    
    (*
    let saveToTemporaryFileBasedOnName (extension:string) : WorkflowFunction<string,FileSystem.FileName,unit> = workflow {
        let! input = getState
        let
        FileSystem.WriteToAsciiFile ()
    }

    let saveToTemporaryFile (extension:string) : WorkflowFunction<string,FileSystem.FileName,unit> = workflow {
        let! input = getState
        let
        FileSystem.WriteToAsciiFile ()
    }
    *)
    
    let saveToFile (outputFile:FileSystem.FileName) : ExogenousWorkflowFunction<string,FileSystem.FileName> = workflow {
        let createPathOfFilename (filename:string)=
            let pathToCreate = System.IO.Path.GetDirectoryName(filename)            
            if pathToCreate <> "" then
                do System.IO.Directory.CreateDirectory pathToCreate |> ignore
            else
                ()
        let! input = getState ()
        let (FileSystem.FileName(outputFileName)) = outputFile
        do createPathOfFilename outputFileName
        do System.IO.File.WriteAllText (outputFileName, input, System.Text.Encoding.ASCII)
        do! updateState outputFile
    }

    let printToFile (outputFile:FileSystem.FileName)
            : EndogenousWorkflowFunction<string> = workflow {
        let! input = getState ()
        let (FileSystem.FileName(outputFileName)) = outputFile
        //do FileSystem.WriteToAsciiFile outputFileName input
        do FileSystem.WriteToAsciiFile outputFileName input
        return ()
    }

    let printToRandomFile (fileExtension:string)
            : WorkflowFunction<string,string,FileSystem.FileName> = workflow {
        let! input = getState ()
        let uuid = System.Guid.NewGuid ()
        let outputFileName = sprintf "%s.%s" (uuid.ToString()) (fileExtension)
        do FileSystem.WriteToAsciiFile outputFileName input
        return (FileSystem.FileName(outputFileName))
    }

    let printToStdout ()
            : EndogenousWorkflowFunction<string> = workflow {
        let! input = getState ()
        printfn "%s" input
        return ()
    }    

    let printObjectToStdout ()
            : EndogenousWorkflowFunction<'a> = workflow {
        let! input = getState ()
        printfn "%+A" input
        return ()
    }    

    let printNewParagraphToStdout<'a,'traceableOfOrigin,'traceableOfModel> ()
            : EndogenousWorkflowFunction<'a> = workflow {
        printfn ""
        printfn ""
        return ()
    }