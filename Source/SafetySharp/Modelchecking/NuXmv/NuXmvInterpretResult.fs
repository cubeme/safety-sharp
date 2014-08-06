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
    | AllSuccessful of Successful:NuXmvCommandResultBasic list
    | OneFailed of Successful:NuXmvCommandResultBasic list * Failed:NuXmvCommandResultBasic
    with
        member this.HasSucceeded () =
            match this with
                | AllSuccessful (_) -> true
                | OneFailed (_,_) -> false
        member this.FailedCommand () =
            match this with
                | AllSuccessful (_) -> None
                | OneFailed (_,failed) -> Some(failed)
        member this.GetResultsOfSuccessfulCommands () =
            match this with
                | AllSuccessful (successful) -> successful
                | OneFailed (successful,_) -> successful
        member this.GetResultsOfAllCommand () =
            match this with
                | AllSuccessful (successful) -> successful
                | OneFailed (successful,failed) -> successful@[failed]
    end
