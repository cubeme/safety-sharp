// The MIT License (MIT)
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

namespace SafetySharp.Internal.Modelchecking.NuXmv

type internal INuXmvCommandResult =
    interface
        abstract member Basic : NuXmvCommandResultBasic
    end

and internal NuXmvCommandResultBasic = {
    Command: ICommand;
    Stderr : string;
    Stdout : string;
}   with
        interface INuXmvCommandResult with
            member this.Basic = this

(*
type internal NuXmvCheckedFormula =
    | Valid of Formula:Formula *  Whitness:Trace option 
    | Undetermined of Formula:Formula
    | Invalid of Formula:Formula * CounterExample:Trace option
    with
        member this.Formula =
            match this with
                | Valid (formula:Formula,_) -> formula
                | Undetermined (formula:Formula) -> formula
                | Invalid (formula:Formula,_) -> formula
*)

(*
type internal NuXmvCommandResultFormula = {
    Command: ICommand;
    Stderr : string;
    Stdout : string;
}
*)

type internal NuXmvInterpretedResult =
    | Successful of Successful:INuXmvCommandResult
    | Failed of Failed:INuXmvCommandResult
    with
        member this.HasSucceeded =
            match this with
                | Successful (_) -> true
                | Failed (_) -> false


type internal NuXmvInterpretedResults =
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
    let splitLines (str:string) =
        str.Split([|"\r\n"; "\n"|],System.StringSplitOptions.None)
    let linesAsExpected (str:string) (expectation:string list) =
        let lines = splitLines str
        if expectation.Length > lines.Length then
            false
        else
            expectation |> List.mapi (fun i elem -> lines.[i].StartsWith(elem))
                        |> List.forall id
    let successFromBool (success:bool) (result:NuXmvCommandResultBasic) : NuXmvInterpretedResult =
        if success then
            NuXmvInterpretedResult.Successful(result)
        else
            NuXmvInterpretedResult.Failed(result)

    let otherwise (result) =
        //pesimistic:
        // NuXmvInterpretedResult.Failed(result)
        //optimistic
        NuXmvInterpretedResult.Successful(result)

    let interpretResultOfNuXmvCommand (result:NuXmvCommandResultBasic) (command:NuXmvCommand) =
        match command with
            | _ -> otherwise result

        
    let interpretResultOfNuSMVCommand (result:NuXmvCommandResultBasic) (command:NuSMVCommand) =
        match command with
            | NuSMVCommand.ReadModel (_) -> otherwise result
            | NuSMVCommand.FlattenHierarchy ->
                let success = linesAsExpected result.Stderr ["Flattening hierarchy...";"...done"]
                successFromBool success result
            | _ -> otherwise result
    
    let interpretResult (result:NuXmvCommandResultBasic) : NuXmvInterpretedResult =
        match result.Command with
            | :? NuSMVCommand as command -> interpretResultOfNuSMVCommand result command
            | :? NuXmvCommand as command -> interpretResultOfNuXmvCommand result command
            //| :? NuXmvCustomCommand as command -> this.ExportCustomCommand command
            //| :? NuXmvStartedCommand as command -> "NuXmv Started"
            | _ -> otherwise result