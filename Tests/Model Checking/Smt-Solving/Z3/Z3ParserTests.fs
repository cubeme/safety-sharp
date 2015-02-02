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

namespace Z3Parser.Tests

open System
open NUnit.Framework
open FParsec

open SafetySharp.Analysis.SmtSolving.SmtLib2.Ast
open SafetySharp.Analysis.SmtSolving.SmtLib2.Parser
open SafetySharp.Analysis.SmtSolving.SmtLib2.Parser.SmtLib2ParsingResult
open SafetySharp.Analysis.SmtSolving.SmtLib2.SMTLIB2Convenience
open SafetySharp.Analysis.SmtSolving.Z3.Ast
open SafetySharp.Analysis.SmtSolving.Z3.Parser

open TestHelpers
open AstTestHelpers

open Z3ExamplesFiles

type Z3OutputExampleTests() =
    let parser = new Z3Parser()
    //let pre = new Predefined("TODO")
    
    let inAstFloat               = inAst<float>
    let inAstPrecision           = inAst<Precision>
    let inAstDepth               = inAst<Depth>
    let inAstExpr                = inAst<Expr>
    let inAstGoalDependencyEntry = inAst<GoalDependencyEntry>
    let inAstGoalDependency      = inAst<GoalDependency>
    let inAstGoal                = inAst<Goal>
    let inAstGoals               = inAst<Goals>

    let parseWithParser parser str =
        match run parser str with
        | Success(result, _, _)   -> (Ast result)
        | Failure(errorMsg, _, _) -> (Error errorMsg)
            
    let parseFloat str               = parseWithParser pfloat str
    let parsePrecision str           = parseWithParser parser.parsePrecision str
    let parseDepth str               = parseWithParser parser.parseDepth str
    let parseExpr str                = parseWithParser parser.parseExpr str
    //let parseGoalDependencyEntry str = parseWithParser parser.parseGoalDependencyEntry str
    //let parseGoalDependency str      = parseWithParser parser.parseGoalDependency str
    let parseGoal str                = parseWithParser parser.parseGoal str
    let parseGoals str               = parseWithParser parser.parseGoals str
    
               
    [<Test>]
    member this.``Datastructure ParsingResult works with convenience function returnAstFloat``() =
        (ParsingResult<float>.Ast 1.25) =? inAstFloat 1.25
        
    [<Test>]
    member this.``a simple float should parse correctly``() =
        parseFloat "1.25" =? inAstFloat 1.25

    [<Test>]
    member this.``"example output: empty goal" should parse correctly``() =
        parseGoal exampleOutputEmptyGoalString =? inAstGoal exampleOutputEmptyGoalAst 

    [<Test>]
    member this.``"example output: empty goals" should parse correctly``() =
        parseGoals exampleOutputEmptyGoalsString =? inAstGoals exampleOutputEmptyGoalsAst 

    [<Test>]
    member this.``"example output file: simplify1b" should parse correctly``() =
        parseGoals exampleOutputFileSimplify1bString =? inAstGoals exampleOutputFileSimplify1bAst 

    
    // http://rise4fun.com/Z3/uzib
    

