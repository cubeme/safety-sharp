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

// example in "Documentation/Workflow/Workflow Engine.md"

module internal Workflow =

    type WorkflowState<'state> = {
        State : 'state;
        StepNumber : int list;
        StepName : string list;
        Log : string list;
        CancellationToken : System.Threading.CancellationToken option; //https://msdn.microsoft.com/de-de/library/dd997364(v=vs.110).aspx
        Tainted : bool; // Use tainted to indicate, if a function changed something. Do not compare states, because now it is obvious, what happens, when a mutable changes
    }
        with
            static member emptyInit =
                {
                    WorkflowState.State = ();
                    WorkflowState.StepNumber = [];
                    WorkflowState.StepName = [];
                    WorkflowState.Log = [];
                    WorkflowState.CancellationToken = None;
                    WorkflowState.Tainted = false;
                }
            static member stateInit (state:'state) =
                {
                    WorkflowState.State = state;
                    WorkflowState.StepNumber = [];
                    WorkflowState.StepName = [];
                    WorkflowState.Log = [];
                    WorkflowState.CancellationToken = None;
                    WorkflowState.Tainted = false;
                }
            member this.CurrentStepNumber = this.StepNumber.Head
            member this.CurrentStepName = this.StepName.Head

    type WorkflowFunction<'oldState,'newState,'returnType> = WorkflowFunction of (WorkflowState<'oldState> -> 'returnType * WorkflowState<'newState>)
    

    let runWorkflowState (WorkflowFunction s) a = s a
    let getWorkflowState = WorkflowFunction (fun s -> (s,s)) //Called in workflow: (implicitly) gets wfState (s) from workflow; assign this State s to the let!; and set (in this case keep) wfState to s
    let getState = WorkflowFunction (fun s -> (s.State,s)) // gets the inner state
    let putWorkflowState s = WorkflowFunction (fun _ -> ((),s)) //Called in workflow: ignore state (_) from workflow; assign nothing () to the let!; and set wfState to the new wfState s
    let putWorkflowStateAndReturn s returnValue = WorkflowFunction (fun _ -> (returnValue,s))//Called in workflow: ignore wfState (_); assign returnValue to the let!; and set wfState to the new wfState s
    
    let updateStateAndReturn<'oldState,'newState,'returnType> (newState:'newState) (returnValue:'returnType) : WorkflowFunction<'oldState,'newState,'returnType> =
        let behavior (wfState:WorkflowState<'oldState>) =
            let newWfState =
                {
                    WorkflowState.State = newState;
                    WorkflowState.StepNumber = wfState.StepNumber;
                    WorkflowState.StepName = wfState.StepName;
                    WorkflowState.Log = wfState.Log;
                    WorkflowState.CancellationToken = wfState.CancellationToken;
                    WorkflowState.Tainted = true;
                }
            returnValue,newWfState
        WorkflowFunction(behavior)

    let updateState<'oldState,'newState> (newState:'newState) : WorkflowFunction<'oldState,'newState,unit> =
        let behavior (wfState:WorkflowState<'oldState>) =
            let newWfState =
                {
                    WorkflowState.State = newState;
                    WorkflowState.StepNumber = wfState.StepNumber;
                    WorkflowState.StepName = wfState.StepName;
                    WorkflowState.Log = wfState.Log;
                    WorkflowState.CancellationToken = wfState.CancellationToken;
                    WorkflowState.Tainted = true;
                }
            (),newWfState
        WorkflowFunction(behavior)
        
    let logEntry<'state> (entry:string) : WorkflowFunction<'state,'state,unit> =
        let behavior (wfState:WorkflowState<'oldState>) =
            do printfn "%s" entry
            let newWfState =
                { wfState with
                    WorkflowState.Log = entry :: wfState.Log;
                    // WorkflowState.Tainted = wfState.Tainted; //tainted keeps old value, because state itself does not get changed!
                }
            (),newWfState            
        WorkflowFunction(behavior)

    let trackSteps_NextStep<'state> (stepName:string) : WorkflowFunction<'state,'state,unit> = 
        let behavior (wfState:WorkflowState<'oldState>) =
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
                
    let trackSteps_CreateSubstepAndEnter<'state> (stepName:string) : WorkflowFunction<'state,'state,unit> = 
        let behavior (wfState:WorkflowState<'oldState>) =
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

    let trackSteps_LeaveSubstep<'state>  : WorkflowFunction<'state,'state,unit> = 
        let behavior (wfState:WorkflowState<'oldState>) =
            let newWfState =
                { wfState with
                    WorkflowState.StepName = wfState.StepName.Tail ;
                    WorkflowState.StepNumber = wfState.StepNumber.Tail;
                    // WorkflowState.Tainted = wfState.Tainted; //tainted keeps old value, because state itself does not get changed!
                }
            (),newWfState            
        WorkflowFunction(behavior)


    let iterateToFixpoint<'state,'returnType> ( (WorkflowFunction(functionToIterate)) : WorkflowFunction<'state,'state,'returnType> ) =
        let adjust_tainted_and_call (wfState:WorkflowState<'state>) : (bool*'returnType*WorkflowState<'state>) =
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
            let (returnValue:'returnType,wfStateAfterCall) = functionToIterate stateButUntainted
            let taintedByCall = wfStateAfterCall.Tainted
            let newWfState =
                { wfStateAfterCall with
                    WorkflowState.Tainted = wasTaintedBefore || taintedByCall;
                }
            (taintedByCall,returnValue,newWfState)
        let rec iterate (wfState:WorkflowState<'state>) : ('returnType*WorkflowState<'state>) =
            let (taintedByCall,returnValue,wfStateAfterOneCall) = adjust_tainted_and_call wfState
            if taintedByCall then
                iterate wfStateAfterOneCall
            else
                (returnValue,wfStateAfterOneCall)
        WorkflowFunction (iterate)
                
    let runWorkflow_getResult (WorkflowFunction s) =
        // no cancellation token
        let result,newWfState = s WorkflowState<unit>.emptyInit
        result
        
    let runWorkflow_getState (WorkflowFunction s) =
        // no cancellation token
        let result,newWfState = s WorkflowState<unit>.emptyInit
        newWfState.State
          
    let runWorkflow_getWfState (WorkflowFunction s) =
        // no cancellation token
        let result,newWfState = s WorkflowState<unit>.emptyInit
        newWfState
          
    let runWorkflowState_getState<'oldState,'newState,'returnType> (WorkflowFunction s:(WorkflowFunction<'oldState,'newState,'returnType>)) (initialState:WorkflowState<'oldState>) =
        let result,newWfState = s (initialState)
        newWfState.State
        
    let runWorkflowState_getWfState<'oldState,'newState,'returnType> (WorkflowFunction s:(WorkflowFunction<'oldState,'newState,'returnType>)) (initialState:WorkflowState<'oldState>) =
        let result,newWfState = s (initialState)
        newWfState
        
    let ignoreResult ( (WorkflowFunction (functionToCall)):WorkflowFunction<'oldState,'newState,'returnType>) : WorkflowFunction<'oldState,'newState,unit> =
        let ignoreResult oldState =
            let result,newState = functionToCall oldState
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
    let readFile<'oldIrrelevantState> (inputFile:string) : WorkflowFunction<'oldIrrelevantState,string,unit> = workflow {
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

    let saveToFile (outputFile:FileSystem.FileName) : WorkflowFunction<string,FileSystem.FileName,unit> = workflow {
        let! input = getState
        let (FileSystem.FileName(outputFileName)) = outputFile
        //do FileSystem.WriteToAsciiFile outputFileName input
        do System.IO.File.WriteAllText (outputFileName, input, System.Text.Encoding.ASCII)
        do! updateState outputFile
    }

    let printToFile (outputFile:FileSystem.FileName) : WorkflowFunction<string,string,unit> = workflow {
        let! input = getState
        let (FileSystem.FileName(outputFileName)) = outputFile
        //do FileSystem.WriteToAsciiFile outputFileName input
        do FileSystem.WriteToAsciiFile outputFileName input
        return ()
    }
