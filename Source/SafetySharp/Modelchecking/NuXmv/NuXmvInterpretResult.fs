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

// Note: 
//  The interpretation code is vulnerable to security attacks which want to provoke
//  wrong results. For example if a quoted variable in a nuXmv model is called
//  "is true" the regular expression "specification .* is true" also matches, if a
//  counter example is given, because it contains the string "is true".
//  Thus the interpretation code is not robust for all input models.
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

module internal Counterexample =
    [<RequireQualifiedAccess>]
    type internal KindOfVariable =
        | State
        | Input
        | Combinatorial

    type internal CounterexampleEntry = {
        VariableName:string;
        Value:string;
        StepNumber:int;
        KindOfVariable:KindOfVariable;
    }
    type internal CounterexampleTrace = {
        Entries: CounterexampleEntry list;
        EntriesOfStep: Map<int,CounterexampleEntry list>; //entries are not required to be sorted
        EntriesOfVariableName: Map<string,CounterexampleEntry list>; //entries should be sorted by stepNumber (ascending)
        // Loops contain a list of states, which the last explicit step could be equivalent to. Loops could contain multiple
        // value from 1..NumberOfLastExplicitStep or no value at all (if verification technique doesn't support loops)
        // Example: If NumberOfLastExplicitStep is 6 and loop is value 2, then
        //             * state-VARs of 6 is state-VARs of 2
        //             * IVARs of 7 is IVARs of 3
        //             * combinatorial vars of 7 is combinatorial vars of 3 (which are result of IVARs of 3(=7) and state-VARS of 2(=6))
        // Thus, with the help of Loop, a infinite trace can be reconstructed with the help of finite entries.
        Loops : int list;
        Type : string;
        Description : string;
    }
    
    let internal counterexampleGroupBy (indexer:CounterexampleEntry->'a) (counterexamples:CounterexampleEntry list) : Map<'a,CounterexampleEntry list> =
        // assume counterexamples are ordered
        // maybe a more efficient solution is possible with List.sortWith or with dictionaries
        // see http://stackoverflow.com/questions/6726559/group-totals-in-f-easy-with-sequences-is-it-possible-with-lists
        counterexamples
            |> List.rev
            |> List.fold (fun groupsAcc counterexample ->
                                let index = indexer counterexample
                                match groupsAcc |> Map.tryFind index with
                                    | Some(s) -> groupsAcc |> Map.remove index |> Map.add index (counterexample::s)
                                    | None -> groupsAcc |> Map.add index [counterexample]
                            ) Map.empty<'a,CounterexampleEntry list>

    let internal parseXml (xmlString:string) : CounterexampleTrace =        
        // TODO: very inefficient (extensive use of XPath and list-concatenations)
        // The basic structure of a counterexample is delivered in counter-example-no-ns.xsd
        // Some remarks:
        //  a <counterexample type=0 desc=Description> looks like:
        //      <counterexample>
        //          <node>
        //                <state id=Id>...
        //                <combinatorial id=Id+1>?...
        //                <input id=Id+1>?
        //          </node>*
        //          <loops>Ids*</loops>?
        //      </counterexample>
        //  a <node> might contain:
        //      <state> with the state values (VARs) of step i.
        //      <input> with the input values (IVARs) of step i+1. An input values of step i can be used to calculate the state values of step i.
        //      <combinatorial> with the combinatorial values of VARs of step i+1. A combinatorial values of step i are DEFINEs, which have as input the resulting value of a VAR in step i-1 and an IVAR of step i. They can be used to calculate the resulting values of step i.    
        // http://stackoverflow.com/questions/332871/f-xml-parsing
        // http://msdn.microsoft.com/de-de/library/d271ytdx(v=vs.110).aspx
        // http://www.w3schools.com/xpath/xpath_syntax.asp
        // From nuXmv chapter 4.8.3 XML Format Printer:
        //  Note that for the last state in the trace, there is no input section in the node tags. This is because the inputs
        //  section gives the new input values which cause the transition to the next state in the trace. There is also no
        //  combinatorial section as this depends on the values of the inputs and are therefore undefined when there are no
        //  inputs.
        let parseNode (xmlNode:System.Xml.XmlNode) : CounterexampleEntry list =
            let parseSection (xmlNode:System.Xml.XmlNode) (kindOfVariable:KindOfVariable) : CounterexampleEntry list =
                let parseValue (xmlNode:System.Xml.XmlNode) (stepNumber:int) : CounterexampleEntry =
                    let varNameNode = xmlNode.SelectSingleNode "./@variable"
                    let varName = varNameNode.InnerText
                    let value = xmlNode.InnerText
                    {
                        CounterexampleEntry.VariableName = varName;
                        CounterexampleEntry.Value = value;
                        CounterexampleEntry.StepNumber = stepNumber;
                        CounterexampleEntry.KindOfVariable = kindOfVariable;
                    }
                // get all entries in this section
                let stepNumberNode = xmlNode.SelectSingleNode "./@id"
                let stepNumber = stepNumberNode.InnerText |> System.Convert.ToInt32
                xmlNode.SelectNodes("./value")
                    |> Seq.cast<System.Xml.XmlNode>
                    |> Seq.map (fun (xmlNode:System.Xml.XmlNode) -> parseValue xmlNode stepNumber)
                    |> List.ofSeq
            // get all entries in this node
            let entriesOfStates =
                xmlNode.SelectNodes("./state")
                    |> Seq.cast<System.Xml.XmlNode>
                    |> Seq.collect (fun (xmlNode:System.Xml.XmlNode) -> parseSection xmlNode KindOfVariable.State)
                    |> List.ofSeq
            let entriesOfCombinatorial =
                xmlNode.SelectNodes("./combinatorial")
                    |> Seq.cast<System.Xml.XmlNode>
                    |> Seq.collect (fun (xmlNode:System.Xml.XmlNode) -> parseSection xmlNode KindOfVariable.Combinatorial)
                    |> List.ofSeq
            let entriesOfInput =
                xmlNode.SelectNodes("./input")
                    |> Seq.cast<System.Xml.XmlNode>
                    |> Seq.collect (fun (xmlNode:System.Xml.XmlNode) -> parseSection xmlNode KindOfVariable.Input)
                    |> List.ofSeq
            // this order guarantees, that entries are sorted by stepNumber, because step of combinatorial and step of input are always step of states+1
            // we assume, that nuxmv outputs the nodes in ascending order and that .SelectNodes returns the nodes in document order
            // see http://msdn.microsoft.com/en-us/library/1212yhbf.aspx
            entriesOfStates@entriesOfCombinatorial@entriesOfInput
        // parse document
        let doc = new System.Xml.XmlDocument()
        doc.LoadXml xmlString
        let docRoot = doc.DocumentElement
        let counterexampleType = docRoot.GetAttribute "type"
        let description = docRoot.GetAttribute "desc"
        let loops =
            let candidates = docRoot.SelectNodes("./loops")
            if candidates.Count = 0 then
                []
            else
                let item = candidates.Item 0 //first item
                let numbersAsString =
                    item.InnerText.Split(',')
                        |> Array.toList
                        |> List.map (fun entry -> entry.Trim())
                let numbers =
                    match numbersAsString with
                        | [""] -> [] //no entry. empty string remains as relict of trim
                        | numbersAsString -> numbersAsString |> List.map (fun entry -> entry |> System.Convert.ToInt32)
                numbers
        let xmlNodes = doc.SelectNodes "./node"
        let entries =
            xmlNodes |> Seq.cast<System.Xml.XmlNode>
                     |> Seq.collect parseNode
                     |> Seq.toList
        // create maps for a convenient access
        let entriesOfStep = entries |> counterexampleGroupBy (fun (entry:CounterexampleEntry) -> entry.StepNumber)  
        let entriesOfVariableName = entries |> counterexampleGroupBy (fun (entry:CounterexampleEntry) -> entry.VariableName)
        {
            CounterexampleTrace.Entries = entries;
            CounterexampleTrace.EntriesOfStep = entriesOfStep;
            CounterexampleTrace.EntriesOfVariableName = entriesOfVariableName;
            CounterexampleTrace.Loops= loops;
            CounterexampleTrace.Type = counterexampleType;
            CounterexampleTrace.Description = description;
        }
        
[<RequireQualifiedAccess>]
type internal CheckOfSpecificationDetailedResult =
    | Valid //of Witness:Counterexample.CounterexampleTrace option 
    | Undetermined
    | Invalid of CounterExample:Counterexample.CounterexampleTrace option
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

    let regexCounterexample = new System.Text.RegularExpressions.Regex("""<[?]xml version="1.0" encoding="UTF-8"[?]>\s*<counter-example.*<\/counter-example>""",regexOption)
    let interpretCounterExample (input:string) : Counterexample.CounterexampleTrace =
        let counterexampleString = regexCounterexample.Match(input).Value
        Counterexample.parseXml counterexampleString
    
    let regexCheckCtlSpecValid = new System.Text.RegularExpressions.Regex("""\A-- specification .* is true([\r])?$""",regexOption) //[\r]? is because on windows systems newline is not \n but \r\n
    let regexCheckCtlSpecInvalid = new System.Text.RegularExpressions.Regex("""\A-- specification .* is false.*^-- as demonstrated by the following execution sequence""",regexOption)
    let interpretResultOfNuSMVCommandCheckCtlSpec (result:NuXmvCommandResultBasic) =
        if linesAsExpectedRegex result.Stdout regexCheckCtlSpecValid then
            {
                NuXmvCommandResultInterpretedCheckOfSpecification.Basic=result;
                NuXmvCommandResultInterpretedCheckOfSpecification.Result=CheckOfSpecificationDetailedResult.Valid;
            }
        elif linesAsExpectedRegex result.Stdout regexCheckCtlSpecInvalid then
            let counterExample = interpretCounterExample result.Stdout
            {
                NuXmvCommandResultInterpretedCheckOfSpecification.Basic=result;
                NuXmvCommandResultInterpretedCheckOfSpecification.Result=CheckOfSpecificationDetailedResult.Invalid(Some(counterExample));
            }
        else
            failwith "result could not be interpreted"
        
    let regexCheckLtlSpecValid = new System.Text.RegularExpressions.Regex("""\A-- specification .* is true([\r])?$""",regexOption) //[\r]? is because on windows systems newline is not \n but \r\n
    let regexCheckLtlSpecInvalid = new System.Text.RegularExpressions.Regex("""\A-- specification .* is false.*^-- as demonstrated by the following execution sequence""",regexOption)
    let interpretResultOfNuSMVCommandCheckLtlSpec (result:NuXmvCommandResultBasic) =
        if linesAsExpectedRegex result.Stdout regexCheckLtlSpecValid then
            {
                NuXmvCommandResultInterpretedCheckOfSpecification.Basic=result;
                NuXmvCommandResultInterpretedCheckOfSpecification.Result=CheckOfSpecificationDetailedResult.Valid;
            }
        elif linesAsExpectedRegex result.Stdout regexCheckLtlSpecInvalid then
            let counterExample = interpretCounterExample result.Stdout
            {
                NuXmvCommandResultInterpretedCheckOfSpecification.Basic=result;
                NuXmvCommandResultInterpretedCheckOfSpecification.Result=CheckOfSpecificationDetailedResult.Invalid(Some(counterExample));
            }
        else
            failwith "result could not be interpreted"
        
    let regexCheckInvarValid = new System.Text.RegularExpressions.Regex("""\A-- invariant .* is true([\r])?$""",regexOption) //[\r]? is because on windows systems newline is not \n but \r\n
    let regexCheckInvarInvalid = new System.Text.RegularExpressions.Regex("""\A-- invariant .* is false.*^-- as demonstrated by the following execution sequence""",regexOption)
    let interpretResultOfNuSMVCommandCheckInvar (result:NuXmvCommandResultBasic) =
        if linesAsExpectedRegex result.Stdout regexCheckInvarValid then
            {
                NuXmvCommandResultInterpretedCheckOfSpecification.Basic=result;
                NuXmvCommandResultInterpretedCheckOfSpecification.Result=CheckOfSpecificationDetailedResult.Valid;
            }
        elif linesAsExpectedRegex result.Stdout regexCheckInvarInvalid then
            let counterExample = interpretCounterExample result.Stdout
            {
                NuXmvCommandResultInterpretedCheckOfSpecification.Basic=result;
                NuXmvCommandResultInterpretedCheckOfSpecification.Result=CheckOfSpecificationDetailedResult.Invalid(Some(counterExample));
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

