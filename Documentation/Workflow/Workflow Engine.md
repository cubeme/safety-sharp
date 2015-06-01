## Workflow

# Example 1 (without trace)

```    
    let initialValue_int (initialValue:int) : WorkflowFunction<_,int,unit> = workflow {
        do! updateState initialValue
    }
 
    let addOne_int_int : WorkflowFunction<int,int,unit> = workflow {
        let! currentValue = getState
        do! updateState (currentValue + 1)
    }
 
    let addOneAndReturn_int_int : WorkflowFunction<int,int,int> =
        let behavior (wfState:WorkflowState<int>) =
            let newState = wfState.State+1
            newState,{wfState with WorkflowState.State=newState; WorkflowState.Tainted=true;}
        WorkflowFunction(behavior)
 
    let addOneTill5_int_int : WorkflowFunction<int,int,unit> =
        let addOneIfSmallerThan5_int_int = workflow {
            let! currentNumber = getState
            if currentNumber < 5 then
                do! addOne_int_int
        }
        iterateToFixpoint addOneIfSmallerThan5_int_int
    
    let convertToString_int_string : WorkflowFunction<int,string,unit> = workflow {
        let! currentValue = getState
        do! updateState (currentValue.ToString())
    }   
    let append_suffix_string_string : WorkflowFunction<string,string,unit> = workflow {
        let! currentValue = getState
        do! updateState (currentValue+"_suffix")        
    }
        
    let demoWorkSpace : WorkflowFunction<unit,string,string> = workflow {
        do! trackSteps_NextStep "set initial value"  
        do! initialValue_int 3
 
        do! trackSteps_NextStep "iterate"
        do! addOneTill5_int_int
 
        do! trackSteps_NextStep "add 1"
        do! addOneAndReturn_int_int |> ignoreResult
 
        do! trackSteps_NextStep "convert to string"
        do! convertToString_int_string
        
        if true then
            do! trackSteps_NextStep "add suffix"
            do! append_suffix_string_string
            //let! result = getState
            return! getState
        else
            return! getState
    }
 
 
    [<EntryPoint>]
    let main argv = 
        printfn "%A" argv
        let resultOfDemo = runWorkflow demoWorkSpace
        printfn "%A" resultOfDemo
        0 // return an integer exit code
```
