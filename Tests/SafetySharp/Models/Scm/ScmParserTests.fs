﻿// The MIT License (MIT)
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

[<TestFixture>]
type ParsingUserStateWorks () =

    let runWithUserState parser str = runParserOnString parser ScmParser.UserState.initialUserState "" str
    
    let parseWithParser parser str =
        match runWithUserState parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, _, _) -> failwith errorMsg
        
    let parseVarIdDecl str = parseWithParser (ScmParser.varIdDecl ) str
    let parseVarIdInst str = parseWithParser (ScmParser.varIdInst ) str

    
    [<Test>]
    member this.``Field declaration has an effect on the user state of the parser`` () =
        let customParser = ScmParser.varIdDecl .>>. (spaces >>. ScmParser.varIdInst .>> eof)
        
        let input = "int1Var int1Var"
        let fullResult = runWithUserState customParser input
        match fullResult with
            | Success(result, userState, _)   ->
                let (decl,inst) = result
                decl =? Var.Var("int1Var")
                inst =? Var.Var("int1Var")
                userState.IsIdentifierOfType "int1Var" ScmParser.IdentifierType.Var =? true
            | Failure(errorMsg, _, _) -> failwith errorMsg
        ()


[<TestFixture>]
type ExampleFiles() =

    let runWithUserState parser str = runParserOnString parser ScmParser.UserState.initialUserState "" str

    let parseWithParser parser str =
        match runWithUserState parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, a, b) -> failwith errorMsg
        
    let parseSCM str = parseWithParser (ScmParser.scmFile .>> eof) str
        
    let parseWithParserAndExpectFailure parser str =
        match runWithUserState parser str with
        | Success(result, _, _)   -> failwith "parsed successfully but expected a parsing failure"
        | Failure(errorMsg, _, _) -> ()

    let parseSCMAndExpectFailure str = parseWithParserAndExpectFailure (ScmParser.scmFile .>> eof) str
    
    //[<Test;Ignore("functionality not implemented yet")>]

    // Tests in order of Examples/SCM/README.md
    // The tests here are in the same order as in the README.md (Note: If you add a new test, keep the order)

    // ## parsing Tests
    [<Test>]
    member this.``Example nestedComponent1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/nestedComponent1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example nestedComponent2 parses successfully`` () =
        let inputFile = """../../Examples/SCM/nestedComponent2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example nestedComponent3 parses successfully`` () =
        let inputFile = """../../Examples/SCM/nestedComponent3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example nestedComponent4 parses successfully`` () =
        let inputFile = """../../Examples/SCM/nestedComponent4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example nestedComponent5 parses successfully`` () =
        let inputFile = """../../Examples/SCM/nestedComponent5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example simpleComponent1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/simpleComponent1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    [<Test>]
    member this.``Example simpleComponent2 parses successfully`` () =
        let inputFile = """../../Examples/SCM/simpleComponent2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example simpleComponent3 parses successfully`` () =
        let inputFile = """../../Examples/SCM/simpleComponent3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
    [<Test>]
    member this.``Example simpleComponent4 parses successfully`` () =
        let inputFile = """../../Examples/SCM/simpleComponent4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example simpleComponent5 parses successfully`` () =
        let inputFile = """../../Examples/SCM/simpleComponent5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example simpleComponent6 parses successfully`` () =
        let inputFile = """../../Examples/SCM/simpleComponent6.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example undeclaredIdentifier1 cannot be parsed`` () =
        let inputFile = """../../Examples/SCM/undeclaredIdentifier1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        parseSCMAndExpectFailure input
        
    [<Test>]
    member this.``Example undeclaredIdentifier2 cannot be parsed`` () =
        let inputFile = """../../Examples/SCM/undeclaredIdentifier2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        parseSCMAndExpectFailure input

    [<Test>]
    member this.``Example undeclaredIdentifier3 cannot be parsed`` () =
        let inputFile = """../../Examples/SCM/undeclaredIdentifier3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        parseSCMAndExpectFailure input

    [<Test>]
    member this.``Example undeclaredIdentifier4 cannot be parsed`` () =
        let inputFile = """../../Examples/SCM/undeclaredIdentifier4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        parseSCMAndExpectFailure input

        
    // ## simple Statements Tests
    [<Test>]
    member this.``Example simpleStatement1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/simpleStatement1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example simpleStatement2 parses successfully`` () =
        let inputFile = """../../Examples/SCM/simpleStatement2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example simpleStatement3 parses successfully`` () =
        let inputFile = """../../Examples/SCM/simpleStatement3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    // ## (cmd)-Tests
    [<Test>]
    member this.``Example cmd1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/cmd1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example cmd2 parses successfully`` () =
        let inputFile = """../../Examples/SCM/cmd2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example cmd3 parses successfully`` () =
        let inputFile = """../../Examples/SCM/cmd3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example cmd4 parses successfully`` () =
        let inputFile = """../../Examples/SCM/cmd4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example cmd5 parses successfully`` () =
        let inputFile = """../../Examples/SCM/cmd5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example cmd6 parses successfully`` () =
        let inputFile = """../../Examples/SCM/cmd6.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        ()

    [<Test>]
    member this.``Example cmd7 parses successfully`` () =
        let inputFile = """../../Examples/SCM/cmd7.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    // ## (beh)-Tests
    [<Test>]
    member this.``Example beh1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/beh1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example beh2 parses successfully`` () =
        let inputFile = """../../Examples/SCM/beh2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example beh3 parses successfully`` () =
        let inputFile = """../../Examples/SCM/beh3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    [<Test>]
    member this.``Example beh4 parses successfully`` () =
        let inputFile = """../../Examples/SCM/beh4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    // ## (call)-Tests (instantaneous)
    [<Test>]
    member this.``Example callInstFromBeh1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callInstFromBeh2 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callInstFromBeh3 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    [<Test>]
    member this.``Example callInstFromBeh4 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callInstFromBeh5 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
    [<Test>]
    member this.``Example callInstFromBeh6 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh6.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callInstFromBeh7 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh7.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callInstFromBeh8 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh8.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
    [<Test>]
    member this.``Example callInstFromProv1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstFromProv1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callInstHierarchy1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
    [<Test>]
    member this.``Example callInstHierarchy2 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callInstHierarchy3 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callInstHierarchy4 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callInstHierarchy5 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    [<Test>]
    member this.``Example callInstHierarchy6 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy6.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callInstHierarchy7 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy7.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    [<Test>]
    member this.``Example callInstHierarchy8 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy8.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callInstHierarchy9 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy9.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    // ## (call)-Tests (delayed)
    [<Test>]
    member this.``Example callDelayedCaution1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callDelayedCaution1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callDelayedCaution2 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callDelayedCaution2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callDelayedSimple1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callDelayedSimple1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
    [<Test>]
    member this.``Example callDelayedInvalid1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callDelayedInvalid1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callDelayedInvalid2 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callDelayedInvalid2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callDelayedInvalid3 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callDelayedInvalid3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callDelayedInvalid4 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callDelayedInvalid4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    [<Test>]
    member this.``Example callDelayedInvalid5 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callDelayedInvalid5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    // ## fault-Tests
    [<Test>]
    member this.``Example nestedComponentWithFaults1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/nestedComponentWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    [<Test>]
    member this.``Example simpleComponentWithFaults1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/simpleComponentWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example simpleComponentWithFaults2 parses successfully`` () =
        let inputFile = """../../Examples/SCM/simpleComponentWithFaults2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    [<Test>]
    member this.``Example simpleComponentWithFaults3 parses successfully`` () =
        let inputFile = """../../Examples/SCM/simpleComponentWithFaults3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    [<Test>]
    member this.``Example behWithFaults1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/behWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callInstFromBehWithFaults1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstFromBehWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()        
        
    [<Test>]
    member this.``Example callInstFromProvWithFaults1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstFromProvWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callInstHierarchyWithFaults1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchyWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    [<Test>]
    member this.``Example callDelayedSimpleWithFaults1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callDelayedSimpleWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    [<Test>]
    member this.``Example dcca1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/dcca1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
                
    // ## Contract-Tests
    [<Test>]
    member this.``Example callInstFromBehWithContract1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstFromBehWithContracts1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callInstHierarchyWithContracts1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchyWithContracts1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example callInstHierarchyWithFaultsAndContract1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchyWithFaultsAndContract1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    // ## Examples which combine several aspects
    (*
    [<Test>]
    member this.``Example exampleDocumentationFull parses successfully`` () =
        let inputFile = """../../Examples/SCM/exampleDocumentationFull.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
    [<Test>]
    member this.``Example exampleDocumentationSimplified1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/exampleDocumentationSimplified1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example exampleDocumentationSimplified2 parses successfully`` () =
        let inputFile = """../../Examples/SCM/exampleDocumentationSimplified2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
    *)
    [<Test>]
    member this.``Example exampleBackupRecovery1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/exampleBackupRecovery1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()

    [<Test>]
    member this.``Example exampleBackupRecovery2 parses successfully`` () =
        let inputFile = """../../Examples/SCM/exampleBackupRecovery2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        
    [<Test>]
    member this.``Example exampleBackupRecovery3 parses successfully`` () =
        let inputFile = """../../Examples/SCM/exampleBackupRecovery3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSCM input
        ()
        