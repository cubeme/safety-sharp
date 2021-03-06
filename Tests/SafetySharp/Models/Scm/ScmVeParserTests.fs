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
type ExampleFormulas () =

    let runWithUserState parser str = runParserOnString parser ScmParser.UserState.initialUserState "" str
    
    let parseWithParser parser str =
        match runWithUserState parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, _, _) -> failwith errorMsg
        
    let parseScm str = parseWithParser (ScmParser.scmFile .>> eof) str

    let parseScmVeLtl us str = SafetySharp.Models.ScmVeParser.ltlExprParser_Result us str
    let parseScmVeProp us str = SafetySharp.Models.ScmVeParser.propositionalExprParser_Result us str
    let parseScmVeLocatedComponent us str = SafetySharp.Models.ScmVeParser.locCompInst_Result us str
        
    
    
    [<Test>]
    member this.``Ltl Formula in  exampleBackupRecovery1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/exampleBackupRecovery1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let scmModel = ScmModel(parseScm input)
        
        let initialParserState = SafetySharp.Models.ScmVeParser.UserState.initialUserState scmModel
                
        let formulaAsString = "[] (backupRecoverySystem.in.sourceValueField == backupRecoverySystem.out.result)"
        let formula =
            let left = (Scm.Comp("in")::Scm.Comp("backupRecoverySystem")::[]),Scm.Field("sourceValueField")
            let right = (Scm.Comp("out")::Scm.Comp("backupRecoverySystem")::[]),Scm.Field("result")
            let equals = ScmVerificationElements.LtlExpr.BExpr(ScmVerificationElements.LtlExpr.ReadField(left),Scm.BOp.Equal,ScmVerificationElements.LtlExpr.ReadField(right) )
            ScmVerificationElements.LtlExpr.LuExpr(equals,ScmVerificationElements.LuOp.Globally)
        
        let parsedFormula = parseScmVeLtl initialParserState formulaAsString
        parsedFormula =? formula
        ()

    [<Test>]
    member this.``Propositional formula in dcca1 parses successfully`` () =
        let inputFile = """../../Examples/SCM/dcca1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let scmModel = ScmModel(parseScm input)
        
        let initialParserState = SafetySharp.Models.ScmVeParser.UserState.initialUserState scmModel
                
        let formulaAsString = "simple.isHazard == true"
        let formula = 
            let readField = ScmVerificationElements.PropositionalExpr.ReadField( ( [Scm.Comp("simple")], Scm.Field("isHazard") ) )
            let trueValue = ScmVerificationElements.PropositionalExpr.Literal(Scm.Val.BoolVal(true))
            ScmVerificationElements.PropositionalExpr.BExpr(readField,Scm.BOp.Equal,trueValue)
        
        let parsedFormula = parseScmVeProp initialParserState formulaAsString
        parsedFormula =? formula
        ()

        
    [<Test>]
    member this.``Located component in default model parses successful`` () =
        let scmModel = ScmHelpers.createEmptyScmModel "simple"        
        let initialParserState = SafetySharp.Models.ScmVeParser.UserState.initialUserState scmModel
                
        let componentLocationAsString = "simple"
        
        let componentLocation = parseScmVeLocatedComponent initialParserState componentLocationAsString
        componentLocation =? [Comp.Comp("simple")]
        ()

        