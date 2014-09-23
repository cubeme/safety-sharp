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
    Constants : string;
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
        let pattern = """\A(?<nl>(\r\n)|\n)Model checking: (?<formula>.*)\k<nl>"""

        new System.Text.RegularExpressions.Regex(pattern)

    static member parseVerificationLog (str:string) = //: PrismVerificationLog =
        let regexMatch = PrismInterpretResult.templateOfVerificationLog.Match(str)
        let formula = (regexMatch.Groups.Item "formula").Value
        formula
    
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