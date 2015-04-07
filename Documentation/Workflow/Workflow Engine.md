## Workflow

# Example 1 (without trace)

```    
    let ex1InitialValue_int (initialValue:int) : LoadWorkflowFunction<int,_,_,unit> = workflow {
        do! updateState initialValue
    }
    
    let ex1AddOne_int_int () : EndogenousWorkflowFunction<int,_,_,unit> = workflow {
        let! currentValue = getState ()
        do! updateState (currentValue + 1)
    }

    // example to show how to do it without "workflow". Omit some annotations.
    let ex1AddOneAndReturn_int_int<'traceableOfOrigin,'traceableOfState> () : EndogenousWorkflowFunction<int,_,_,int> =
        let behavior (wfState:WorkflowState<int,'traceableOfOrigin,'traceableOfState>) =
            let newState = wfState.State+1
            newState,{wfState with WorkflowState.State=newState; WorkflowState.Tainted=true;}
        WorkflowFunction(behavior)

    // example to show how to do it with the generic workflow type. Omit some annotations. Possible, because it is a function.
    let ex1AddOneTill5_int_int () : WorkflowFunction<int,int,_,_,_,_,unit> =
        let addOneIfSmallerThan5_int_int = workflow {
            let! currentNumber = getState ()
            if currentNumber < 5 then
                do! ex1AddOne_int_int ()
        }
        iterateToFixpoint addOneIfSmallerThan5_int_int
    
    let ex1ConvertToString_int_string () : ExogenousWorkflowFunction<int,string,_,_,_,unit> = workflow {
        let! currentValue = getState ()
        do! updateState (currentValue.ToString())
    }   

    // example to show how to do it with the generic workflow type. Omit some annotations. Possible, because it is a function.
    let ex1Append_suffix_string_string () : WorkflowFunction<string,string,_,_,_,_,unit> = workflow {
        let! currentValue = getState ()
        do! updateState (currentValue+"_suffix")        
    }
        
    let ex1DemoWorkflow () : InitialWorkflowFunction<_,_,_,_> = workflow {
        do! trackSteps_NextStep "set initial value"  
        do! ex1InitialValue_int 3

        do! trackSteps_NextStep "iterate"
        do! ex1AddOneTill5_int_int ()

        do! trackSteps_NextStep "add 1"
        do! ex1AddOneAndReturn_int_int () |> ignoreResult

        do! trackSteps_NextStep "convert to string"
        do! ex1ConvertToString_int_string ()
        
        if true then
            do! trackSteps_NextStep "add suffix"
            do! ex1Append_suffix_string_string ()
            //let! result = getState
            return! getState ()
        else
            return! getState ()
    }	
	
    [<EntryPoint>]
    let main argv = 
        printfn "%A" argv
        let resultOfExample1 = runWorkflow_getResult (ex1DemoWorkflow())
        printfn "%A" resultOfExample1
        0 // return an integer exit code
```

# Example 2 (with trace)

```
    let ex2InitialValue_int (initialValue:int) : LoadWorkflowFunction<int,_,_,unit> = workflow {
        do! updateState initialValue
        do! initializeTracer ([initialValue])
    }
    
    let ex2AddOne_int_int () : EndogenousWorkflowFunction<int,_,_,unit> = workflow {
        let! currentValue = getState ()
        let newValue = currentValue + 1
        do! updateState (newValue)
        
        let mapInClosure = Map.empty<int,int>.Add(currentValue,newValue)
        let intermediateTracer (oldValue:int) = mapInClosure.Item oldValue
        do! updateTracer intermediateTracer
    }

    // example to show how to do it without "workflow". Omit some annotations.
    let ex2AddOneAndReturn_int_int<'traceableOfOrigin> () : EndogenousWorkflowFunction<int,_,_,int> =
        let behavior (wfState:WorkflowState<int,'traceableOfOrigin,int>) =
            let currentValue = wfState.State
            let newValue = currentValue + 1

            let mapInClosure = Map.empty<int,int>.Add(currentValue,newValue)            
            let newTracer (toTrace) =
                let toOldTraceEnd = wfState.ForwardTracer toTrace
                let intermediateTracer (oldValue:int) =
                    mapInClosure.Item oldValue
                intermediateTracer toOldTraceEnd
            let intermediateTracer (oldValue:int) = mapInClosure.Item oldValue
            
            let newWfState =
                { wfState with
                    WorkflowState.State=newValue;
                    WorkflowState.ForwardTracer=newTracer
                    WorkflowState.Tainted=true;
                }

            newValue,newWfState
        WorkflowFunction(behavior)

    // example to show how to do it with the generic workflow type. Omit some annotations. Possible, because it is a function.
    let ex2AddOneTill5_int_int () : WorkflowFunction<int,int,_,_,_,_,unit> =
        let addOneIfSmallerThan5_int_int = workflow {
            let! currentNumber = getState ()
            if currentNumber < 5 then
                do! ex2AddOne_int_int () //this function already keeps the trace
        }
        iterateToFixpoint addOneIfSmallerThan5_int_int
    
    let ex2ConvertToString_int_string () : ExogenousWorkflowFunction<int,string,_,_,_,unit> = workflow {
        let! currentValue = getState ()
        let newValue = currentValue.ToString()
        do! updateState (newValue)
        
        let mapInClosure = Map.empty<int,string>.Add(currentValue,newValue)
        let intermediateTracer (oldValue:int) = mapInClosure.Item oldValue
        do! updateTracer intermediateTracer
    }   

    // example to show how to do it with the generic workflow type. Omit some annotations. Possible, because it is a function.
    let ex2Append_suffix_string_string () : WorkflowFunction<string,string,_,_,_,_,unit> = workflow {
        let! currentValue = getState ()
        let newValue = currentValue+"_suffix"
        do! updateState (newValue)

        let mapInClosure = Map.empty<string,string>.Add(currentValue,newValue)
        let intermediateTracer (oldValue:string) = mapInClosure.Item oldValue
        do! updateTracer intermediateTracer
    }
        
    let ex2DemoWorkflow () : InitialWorkflowFunction<_,_,_,_> = workflow {
        do! trackSteps_NextStep "set initial value"  
        do! ex2InitialValue_int 3

        do! trackSteps_NextStep "iterate"
        do! ex2AddOneTill5_int_int ()

        do! trackSteps_NextStep "add 1"
        do! ex2AddOneAndReturn_int_int () |> ignoreResult

        do! trackSteps_NextStep "convert to string"
        do! ex2ConvertToString_int_string ()
        
        if true then
            do! trackSteps_NextStep "add suffix"
            do! ex2Append_suffix_string_string ()
            //let! result = getState
            return! getState ()
        else
            return! getState ()
    }
	
    [<EntryPoint>]
    let main argv = 
        printfn "%A" argv
        let resultOfExample2,wfStateOfExample2 = runWorkflow_getResultAndWfState (ex2DemoWorkflow())
        printfn "%A" resultOfExample2
        
        printfn "traces:"
        let printTracables (var:int) =
            printfn "from: %d to: %s" (var) (wfStateOfExample2.ForwardTracer var)
        wfStateOfExample2.TraceablesOfOrigin |> List.iter printTracables
        0 // return an integer exit code
```