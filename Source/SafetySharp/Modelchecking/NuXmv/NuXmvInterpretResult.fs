﻿// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

// Note: 
//  The interpretation code is vulnerable to security attacks which want to provoke
//  wrong results. For example if a quoted variable in a nuXmv model is called
//  "is true" the regular expression regexCheckCtlSpecValid also matches, if a
//  counter example is given. Thus the interpretation code could not be applied
//  to all kinds of models.
// TODO:
//   - More accurate interpretation, which doesn't allow these kind of attacks
//   - Tests for those attacks


namespace SafetySharp.Internal.Modelchecking.NuXmv

// It is nice to be able to show the reason for a failure of the processing of a command in the GUI
[<RequireQualifiedAccess>]
type CommandResultProcessingFailure =
    | NuXmvShutdown
    | NotDeterminedYet
    | Unclear
    | SyntacticalError
    | SemanticalError
    | ExecutionTimeExceeded

type internal INuXmvCommandResult =
    interface
        abstract member Basic : NuXmvCommandResultBasic
        abstract member HasSucceeded : bool
    end

and internal NuXmvCommandResultBasic = {
    Command : ICommand;
    Stderr : string;
    Stdout : string;
    Failure : CommandResultProcessingFailure option;
}   with
        interface INuXmvCommandResult with
            member this.Basic = this
            member this.HasSucceeded =
                this.Failure.IsNone
        // to allow access without casting to ":> INuXmvCommandResult"
        member this.HasSucceeded =
                this.Failure.IsNone

type Trace() =
    class end

[<RequireQualifiedAccess>]
type internal CheckOfSpecificationDetailedResult =
    | Valid of Witness:Trace option 
    | Undetermined
    | Invalid of CounterExample:Trace option
    with
        member this.IsSpecValid =
            match this with
                | CheckOfSpecificationDetailedResult.Valid(_) -> true
                | _ -> false
        member this.IsSpecInvalid =
            match this with
                | CheckOfSpecificationDetailedResult.Invalid(_) -> true
                | _ -> false
        member this.IsSpecUndetermined =
            match this with
                | CheckOfSpecificationDetailedResult.Undetermined -> true
                | _ -> false

type internal NuXmvCommandResultInterpretedCheckOfSpecification = {
    Basic : NuXmvCommandResultBasic;
    Result : CheckOfSpecificationDetailedResult;
}

type internal NuXmvCommandResultInterpretedCheckFsm = {
    Basic : NuXmvCommandResultBasic;
    IsTotal : bool;
    IsDeadlockFree : bool;
}
    with
        interface INuXmvCommandResult with
            member this.Basic = this.Basic
            member this.HasSucceeded =
                this.Basic.HasSucceeded
        member this.HasSucceeded =
                this.Basic.HasSucceeded



type internal NuXmvCommandResultInterpretedBasic = {
    Basic : NuXmvCommandResultBasic;
    Successful : bool;
}
    with
        interface INuXmvCommandResult with
            member this.Basic = this.Basic
            member this.HasSucceeded =
                this.Successful
        member this.HasSucceeded =
                this.Successful
    

type internal NuXmvCommandResultsInterpreted =
    | AllSuccessful of Successful:INuXmvCommandResult list
    | OneFailed of Successful:INuXmvCommandResult list * Failed:INuXmvCommandResult
    with
        member this.HasSucceeded =
            match this with
                | AllSuccessful (_) -> true
                | OneFailed (_,_) -> false
        member this.FailedCommand =
            match this with
                | AllSuccessful (_) -> None
                | OneFailed (_,failed) -> Some(failed)
        member this.GetResultsOfSuccessfulCommands =
            match this with
                | AllSuccessful (successful) -> successful
                | OneFailed (successful,_) -> successful
        member this.GetResultsOfAllCommand =
            match this with
                | AllSuccessful (successful) -> successful
                | OneFailed (successful,failed) -> successful@[failed]
        member this.GetBasicResultsOfAllCommand =
            match this with
                | AllSuccessful (successful) -> successful |> List.map (fun result -> result.Basic)
                | OneFailed (successful,failed) -> successful@[failed] |> List.map (fun result -> result.Basic)
    end

module internal NuXmvInterpretResult =
    //////////////////////////////////////
    // helpers
    //////////////////////////////////////


    let splitLines (str:string) =
        str.Split([|"\r\n"; "\n"|],System.StringSplitOptions.None)

    let linesAsExpectedStr (str:string) (expectation:string list) =
        let lines = splitLines str
        if expectation.Length > lines.Length then
            false
        else
            expectation |> List.mapi (fun i elem -> lines.[i].StartsWith(elem))
                        |> List.forall id
    let linesAsExpectedRegex (str:string) (regex:System.Text.RegularExpressions.Regex) =
        regex.IsMatch(str)
    
    // this should only be used for commands, where the result doesn't need further interpretation
    let successFromBool (success:bool) (result:NuXmvCommandResultBasic) : INuXmvCommandResult =
        let newResult =
            if success then 
                {
                    NuXmvCommandResultInterpretedBasic.Basic=result;
                    NuXmvCommandResultInterpretedBasic.Successful=true;
                }
            else
                {
                    NuXmvCommandResultInterpretedBasic.Basic= {result with NuXmvCommandResultBasic.Failure=Some(CommandResultProcessingFailure.Unclear)};
                    NuXmvCommandResultInterpretedBasic.Successful=false;
                }
        newResult :> INuXmvCommandResult
            
    // this should only be used for commands, where the result doesn't need further interpretation
    let otherwise (result:NuXmvCommandResultBasic) : INuXmvCommandResult=
        successFromBool (result.HasSucceeded) result

    let regexOption = System.Text.RegularExpressions.RegexOptions.Singleline ||| System.Text.RegularExpressions.RegexOptions.Multiline
    
    //////////////////////////////////////
    // interpretation of concrete commands
    //////////////////////////////////////

    // note: regular expressions are on top level to avoid multiple initializations
    //       nice to test regular expressions on the fly: http://www.rubular.com/
    //       for examples see file NuXmvInterpretResultTests
    //       http://stackoverflow.com/questions/851057/how-to-prevent-regular-expression-of-hang-or-set-time-out-for-it-in-net
    //       http://www.regular-expressions.info/catastrophic.html
        
    let regexReadModel = new System.Text.RegularExpressions.Regex("""\AParsing file \".*\" [.][.][.][.][.] done[.]""")
    let interpretResultOfNuSMVCommandReadModel (result:NuXmvCommandResultBasic) =
        let success = linesAsExpectedRegex result.Stderr regexReadModel
        successFromBool success result

    let interpretResultOfNuSMVCommandFlattenHierarchy (result:NuXmvCommandResultBasic) =
        let success = linesAsExpectedStr result.Stderr ["Flattening hierarchy...";"...done"]
        successFromBool success result
            
    let regexCheckFsmTotal = new System.Text.RegularExpressions.Regex("""^The transition relation is total""",regexOption)
    let regexCheckFsmNotTotalWithDeadlock = new System.Text.RegularExpressions.Regex("""^The transition relation is not total.*The transition relation is not deadlock-free""",regexOption)
    let regexCheckFsmNotTotalWithoutDeadlock = new System.Text.RegularExpressions.Regex("""^The transition relation is not total.*so the machine is deadlock-free""",regexOption)
    let interpretResultOfNuSMVCommandCheckFsm (result:NuXmvCommandResultBasic) =
        if linesAsExpectedRegex result.Stdout regexCheckFsmTotal then
            {
                NuXmvCommandResultInterpretedCheckFsm.Basic=result;
                NuXmvCommandResultInterpretedCheckFsm.IsDeadlockFree=true;
                NuXmvCommandResultInterpretedCheckFsm.IsTotal=true;
            }
        elif linesAsExpectedRegex result.Stdout regexCheckFsmNotTotalWithDeadlock then
            // TODO: In many cases it doesn't make sense to continue the verification if the Kripke-Structure contains a deadlock
            //       we could rewrite the basic result to HasSucceeded:=false                    
            {
                NuXmvCommandResultInterpretedCheckFsm.Basic=result;
                NuXmvCommandResultInterpretedCheckFsm.IsDeadlockFree=false;
                NuXmvCommandResultInterpretedCheckFsm.IsTotal=false;
            }
        elif linesAsExpectedRegex result.Stdout regexCheckFsmNotTotalWithoutDeadlock then
            {
                NuXmvCommandResultInterpretedCheckFsm.Basic=result;
                NuXmvCommandResultInterpretedCheckFsm.IsDeadlockFree=true;
                NuXmvCommandResultInterpretedCheckFsm.IsTotal=false;
            }
        else
            failwith "result of check_fsm could not be interpreted"

    let interpretCounterExample (counterExample:string) : Trace =
        Trace()
    
    //TODO: Assure, the string is tested from the beginning of the first line!!!
    let regexCheckCtlSpecValid = new System.Text.RegularExpressions.Regex("""\A-- specification .* is true""",regexOption)
    let regexCheckCtlSpecInvalid = new System.Text.RegularExpressions.Regex("""\A-- specification .* is false.*^-- as demonstrated by the following execution sequence""",regexOption)
    let interpretResultOfNuSMVCommandCheckCtlSpec (result:NuXmvCommandResultBasic) =
        if linesAsExpectedRegex result.Stdout regexCheckCtlSpecValid then
            {
                NuXmvCommandResultInterpretedCheckOfSpecification.Basic=result;
                NuXmvCommandResultInterpretedCheckOfSpecification.Result=CheckOfSpecificationDetailedResult.Valid(None);
            }
        elif linesAsExpectedRegex result.Stdout regexCheckCtlSpecInvalid then                   
            {
                NuXmvCommandResultInterpretedCheckOfSpecification.Basic=result;
                NuXmvCommandResultInterpretedCheckOfSpecification.Result=CheckOfSpecificationDetailedResult.Invalid(None);
            }
        else
            failwith "result could not be interpreted"
        
    let regexCheckLtlSpecValid = new System.Text.RegularExpressions.Regex("""\A-- specification .* is true""",regexOption)
    let regexCheckLtlSpecInvalid = new System.Text.RegularExpressions.Regex("""\A-- specification .* is false.*^-- as demonstrated by the following execution sequence""",regexOption)
    let interpretResultOfNuSMVCommandCheckLtlSpec (result:NuXmvCommandResultBasic) =
        if linesAsExpectedRegex result.Stdout regexCheckLtlSpecValid then
            {
                NuXmvCommandResultInterpretedCheckOfSpecification.Basic=result;
                NuXmvCommandResultInterpretedCheckOfSpecification.Result=CheckOfSpecificationDetailedResult.Valid(None);
            }
        elif linesAsExpectedRegex result.Stdout regexCheckLtlSpecInvalid then                   
            {
                NuXmvCommandResultInterpretedCheckOfSpecification.Basic=result;
                NuXmvCommandResultInterpretedCheckOfSpecification.Result=CheckOfSpecificationDetailedResult.Invalid(None);
            }
        else
            failwith "result could not be interpreted"
        
    let regexCheckInvarValid = new System.Text.RegularExpressions.Regex("""\A-- invariant .* is true""",regexOption)
    let regexCheckInvarInvalid = new System.Text.RegularExpressions.Regex("""\A-- invariant .* is false.*^-- as demonstrated by the following execution sequence""",regexOption)
    let interpretResultOfNuSMVCommandCheckInvar (result:NuXmvCommandResultBasic) =
        if linesAsExpectedRegex result.Stdout regexCheckInvarValid then
            {
                NuXmvCommandResultInterpretedCheckOfSpecification.Basic=result;
                NuXmvCommandResultInterpretedCheckOfSpecification.Result=CheckOfSpecificationDetailedResult.Valid(None);
            }
        elif linesAsExpectedRegex result.Stdout regexCheckInvarInvalid then                   
            {
                NuXmvCommandResultInterpretedCheckOfSpecification.Basic=result;
                NuXmvCommandResultInterpretedCheckOfSpecification.Result=CheckOfSpecificationDetailedResult.Invalid(None);
            }
        else
            failwith "result could not be interpreted"

    //////////////////////////////////////
    // interpretation of abstract commands
    //////////////////////////////////////
    

    let interpretResultOfNuXmvCommand (result:NuXmvCommandResultBasic) (command:NuXmvCommand) : INuXmvCommandResult =
        match command with
            | _ -> otherwise result

        
    let interpretResultOfNuSMVCommand (result:NuXmvCommandResultBasic) (command:NuSMVCommand) : INuXmvCommandResult =
        match command with
            | NuSMVCommand.ReadModel (_) ->    interpretResultOfNuSMVCommandReadModel result
            | NuSMVCommand.FlattenHierarchy -> interpretResultOfNuSMVCommandFlattenHierarchy result 
            | NuSMVCommand.CheckFsm ->         (interpretResultOfNuSMVCommandCheckFsm result) :> INuXmvCommandResult
            | _ -> otherwise result
    
    let interpretResult (result:NuXmvCommandResultBasic) : INuXmvCommandResult =
        match result.Command with
            | :? NuSMVCommand as command -> interpretResultOfNuSMVCommand result command
            | :? NuXmvCommand as command -> interpretResultOfNuXmvCommand result command
            //| :? NuXmvCustomCommand as command -> this.ExportCustomCommand command
            //| :? NuXmvStartedCommand as command -> "NuXmv Started"
            | _ -> otherwise result

