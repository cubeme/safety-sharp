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

namespace SafetySharp.Analysis.Modelchecking.PromelaSpin

open System
open System.IO
open FParsec

module internal PanInterpretResult =

    [<RequireQualifiedAccess>]
    type PanVerificationResult =
        | True
        | False
        | Maybe

    type PanVerificationLog = {
        SpinVersion : string;
        StateVectorSize : string;
        DepthReached : string;
        Errors : string;
        CheckingTime : string;
        Result : PanVerificationResult;
        FullLog : string;
    }

    let templateOfVerificationLog = 
        let pattern =
              """(?<preamble>[\w\W]*?)""" // atomic group. everything before next token. Tried """(?<preamble>(([\w\W]?!\(Spin)*))""", worked, but didn't capture.
            + """\(Spin Version (?<version>.*) --(\w|\s)+\)"""
            + """(?<nl>(\r\n)|\n)""" //Give newline a name
            + """((\r\n)|\n|.)*?""" // not important. Lazy
            + """State-vector (?<stateVector>.*), depth reached (?<depthReached>.*), (••• )?errors: (?<errors>\d+)( •••)?\k<nl>"""
            + """((\r\n)|\n|.)*?""" // not important. Lazy
            + """pan: elapsed time (?<timeMC>.*) seconds"""
        new System.Text.RegularExpressions.Regex(pattern)
        
    let parseVerificationLog (str:string) : PanVerificationLog =
        let regexMatch = templateOfVerificationLog.Match(str)
        if regexMatch.Groups.Count <= 1 then
            {
                PanVerificationLog.SpinVersion = "unknown";
                PanVerificationLog.StateVectorSize = "0 byte";
                PanVerificationLog.DepthReached = "0";
                PanVerificationLog.Errors = "1";
                PanVerificationLog.CheckingTime = "0 seconds";
                PanVerificationLog.Result = PanVerificationResult.Maybe;
                PanVerificationLog.FullLog = str;
            }
        else
            let preamble = (regexMatch.Groups.Item "preamble").Value
            let version = (regexMatch.Groups.Item "version").Value
            let stateVector = (regexMatch.Groups.Item "stateVector").Value
            let depthReached = (regexMatch.Groups.Item "depthReached").Value
            let errors = (regexMatch.Groups.Item "errors").Value
            //let yes =
            //    let value = (regexMatch.Groups.Item "yes").Value
            //    Int32.Parse value
            let timeMC = (regexMatch.Groups.Item "timeMC").Value
            let result =
                if errors.Equals "0" then
                    if preamble.Contains "error: max search depth too small"then
                        PanVerificationResult.Maybe
                    else
                        PanVerificationResult.True
                else                
                    if preamble.Contains "end state in claim reached" || preamble.Contains "assertion violated"  then
                        PanVerificationResult.False
                    else
                        PanVerificationResult.Maybe
            {
                PanVerificationLog.SpinVersion = version;
                PanVerificationLog.StateVectorSize = stateVector;
                PanVerificationLog.DepthReached = depthReached;
                PanVerificationLog.Errors = errors;
                PanVerificationLog.CheckingTime = timeMC;
                PanVerificationLog.Result = result;
                PanVerificationLog.FullLog = str;
            }
            
    open SafetySharp.Workflow

    let interpretWorkflow<'traceableOfOrigin> ()
            : ExogenousWorkflowFunction<string,PanVerificationLog> = workflow {
        let! state = getState ()
        let interpretation = parseVerificationLog state
        do! updateState interpretation
    }