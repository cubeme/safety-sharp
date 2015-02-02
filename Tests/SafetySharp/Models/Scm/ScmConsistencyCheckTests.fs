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

namespace Models.Scm


open System
open NUnit.Framework
open FParsec

open TestHelpers
open AstTestHelpers
open SafetySharp.Models
open SafetySharp.Models.Scm
open SafetySharp.Models.ScmHelpers
open SafetySharp.Models.ScmRewriterBase
open SafetySharp.Models.ScmRewriterLevelUp
open SafetySharp.Models.ScmRewriterConvertFaults
open SafetySharp.Models.ScmRewriterInlineBehavior
open SafetySharp.Models.ScmRewriterFlattenModel

[<TestFixture>]
type ScmConsistencyCheckOfDelayedBindingsTests () =    


    let runWithUserState parser str = runParserOnString parser ScmParser.UserState.initialUserState "" str

    let parseWithParser parser str =
        match runWithUserState parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, a, b) -> failwith errorMsg
        
    let parseSCM str = parseWithParser (ScmParser.scmFile .>> eof) str
        
    

    [<Test>]
    member this.``Consistency check detects no failure in example callDelayedSimple1 `` () =
        let inputFile = """../../Examples/SCM/callDelayedSimple1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        ScmConsistencyCheck.``check if Main Steps make at most one delayed call (transitive)`` model =? true
        //ScmConsistencyCheck.``check if ProvPorts of model's root make at most one delayed call (transitive)`` model =? true
        ()

    [<Test>]
    member this.``Example callDelayedInvalid1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callDelayedInvalid1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        ScmConsistencyCheck.``check if Main Steps make at most one delayed call (transitive)`` model =? false
        ()

    [<Test>]
    member this.``Example callDelayedInvalid2 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callDelayedInvalid2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        ScmConsistencyCheck.``check if Main Steps make at most one delayed call (transitive)`` model =? true
        ()

    [<Test>]
    member this.``Example callDelayedInvalid3 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callDelayedInvalid3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        ScmConsistencyCheck.``check if Main Steps make at most one delayed call (transitive)`` model =? true
        ()

    [<Test>]
    member this.``Example callDelayedInvalid4 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callDelayedInvalid4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        ScmConsistencyCheck.``check if Main Steps make at most one delayed call (transitive)`` model =? true
        ()
        
    [<Test>]
    member this.``Example callDelayedInvalid5 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callDelayedInvalid5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        ScmConsistencyCheck.``check if Main Steps make at most one delayed call (transitive)`` model =? true
        ()