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

namespace SafetySharp.Internal.Modelchecking.Prism

open System
open System.IO
open FParsec

type PrismInitialEntry = {
    PrismVersion : string;
    DateOfVerificationRun : string;
    CommandLine : string;
    ModelFile : string;
    PropertiesFile : string;
    Properties : string;
    ModelCheckingType : string;
    //...
}

[<RequireQualifiedAccess>]
type PrismVerificationResult =
    | True
    | False
    | Maybe

type PrismVerificationLog = {
    Property : string;
    Constants : (string*string) list;
    Prob0Time : string; //Prob0 calculates states with a fast algorithm, which do _not_ fulfill the property for sure
    Prob0States : int; //Number of States, which do _not_ fulfill the property for sure
    Prob1Time : string; //Prob0 calculates states with a fast algorithm, which _do_ fulfill the property for sure
    Prob1States : int; //Number of States, which _do_ fulfill the property for sure
    MaybeStates : int;
    Result : PrismVerificationResult;
}

type PrismInterpretResult () =
    static member templateOfVerificationLog = 
        // Idea was to use some kind of "reverse template"
        // for simple cases without recursive or optional entries.
        // see http://stackoverflow.com/questions/5346158/parse-string-using-format-template
        //     http://www.rexegg.com/regex-capture.html
        //     http://stackoverflow.com/questions/906493/regex-named-capturing-groups-in-net    
        let pattern =
              """\A(?<nl>(\r\n)|\n)""" //It starts with a newline. Give newline a name
            + """Model checking: (?<formula>.*)\k<nl>"""
            + """(Property constants: (?<constants>.*)\k<nl>)?"""
            + """\k<nl>"""
            + """Prob0: (?<prob0>.*)\k<nl>"""
            + """\k<nl>"""
            + """Prob1: (?<prob1>.*)\k<nl>"""
            + """\k<nl>"""
            + """yes = (?<yes>.*), no = (?<no>.*), maybe = (?<maybe>.*)\k<nl>"""
            + """\k<nl>"""
            + """Computing remaining probabilities[.][.][.]\k<nl>"""
            + """Engine: (?<engine>.*)\k<nl>"""
            + """\k<nl>"""
            + """(?<enginestats>(?>.+\k<nl>)+)""" //Collect all lines, which at least contain one character. Stops when line starts with a newline. To prevent an explosion (see http://www.rexegg.com/regex-explosive-quantifiers.html) we use an atomic group ?>.
            + """\k<nl>"""
            + """Starting iterations[.][.][.]\k<nl>"""
            + """\k<nl>"""
            + """(?<iterations>.*)\k<nl>"""
            + """\k<nl>"""
            + """(?<probabilities>(?>.+\k<nl>)+)""" //Collect all lines, which at least contain one character. Stops when line starts with a newline. To prevent an explosion (see http://www.rexegg.com/regex-explosive-quantifiers.html) we use an atomic group ?>.
            + """\k<nl>"""
            + """Number of states satisfying .*: (?<satisfyingStates>.*)\k<nl>"""
            + """\k<nl>"""
            + """Property satisfied in (?<satisfyingInitialStates>.*) of (?<initialStates>.*) initial states[.]\k<nl>"""
            + """\k<nl>"""
            + """Time for model checking: (?<timeMC>.*)[.]\k<nl>"""
            + """\k<nl>"""
            + """Result: (?<result>.*)\k<nl>"""
        //TODO: There might also be a pattern for other results. E.g. if there are no maybe-states
        new System.Text.RegularExpressions.Regex(pattern)

        
    // TODO: Parse
    //  - P=?
    //  - R=?
    //  - R>x
    //  - AG ...
    //  - ...
    //  - Output needs no checking
    //  - "Degraded" Mode, which only parses part of the content (success or no success) if other regex fail
    // TODO: Is there a witness or counterexample on command line?!? Formula "E [ F s= 7]" in dice in GUI offers to show a witness.



    // only works for P>x []...
    static member parseVerificationLog (str:string) = //: PrismVerificationLog =
        let regexMatch = PrismInterpretResult.templateOfVerificationLog.Match(str)
        let formula = (regexMatch.Groups.Item "formula").Value
        let constants =
            let regexMatchOfConstant = regexMatch.Groups.Item "constants"
            if regexMatchOfConstant.Success then
                let values = regexMatchOfConstant.Value
                let assignments = values.Split(',')
                assignments |> Array.toList
                            |> List.map (fun elem -> let splitted = elem.Split('=')
                                                     (splitted.[0],splitted.[1])
                                         )
            else
                []
        let prob0 = (regexMatch.Groups.Item "prob0").Value
        let prob1 = (regexMatch.Groups.Item "prob1").Value
        let yes =
            let value = (regexMatch.Groups.Item "yes").Value
            Int32.Parse value
        let no =
            let value = (regexMatch.Groups.Item "no").Value
            Int32.Parse value
        let maybe =
            let value = (regexMatch.Groups.Item "maybe").Value
            Int32.Parse value
        let engine = (regexMatch.Groups.Item "engine").Value
        let enginestats = (regexMatch.Groups.Item "enginestats").Value
        let iterations = (regexMatch.Groups.Item "iterations").Value
        let probabilities = (regexMatch.Groups.Item "probabilities").Value
        let satisfyingStates = (regexMatch.Groups.Item "satisfyingStates").Value
        let satisfyingInitialStates = (regexMatch.Groups.Item "satisfyingInitialStates").Value
        let initialStates = (regexMatch.Groups.Item "initialStates").Value
        let timeMC = (regexMatch.Groups.Item "timeMC").Value
        let result =
            let result = (regexMatch.Groups.Item "result").Value
            if result.StartsWith "true" then
                PrismVerificationResult.True
            else
                failwith "NotImplementedYet"
        {
            PrismVerificationLog.Property = formula;
            PrismVerificationLog.Constants = constants;
            PrismVerificationLog.Prob0Time = prob0;
            PrismVerificationLog.Prob0States = no;
            PrismVerificationLog.Prob1Time = prob1;
            PrismVerificationLog.Prob1States = yes;
            PrismVerificationLog.MaybeStates = maybe;
            PrismVerificationLog.Result = result;
        }
    
    (*
    member this.Parse parser input =
        match run parser input with
            | Success(result, _, _)
                -> result
            | Failure(msg, error, _)
                ->  let writer = new StringWriter()
                    error.WriteTo(writer, null, columnWidth = 200)
                    let error = writer.ToString();
                    writer.Dispose();
                    failwith error

    *)