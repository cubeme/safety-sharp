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

namespace SafetySharp.Internal.SmtSolving.Z3.Parser

open System
open System.IO
open FParsec
open SafetySharp.Internal.SmtSolving.SmtLib2.Parser.SmtLib2ParsingResult
open SafetySharp.Internal.SmtSolving.SmtLib2.Ast
open SafetySharp.Internal.SmtSolving.Z3.Ast
open SafetySharp.Internal.SmtSolving.SmtLib2.Parser
open SafetySharp.Internal.SmtSolving.SmtLib2.Parser.ParseSMTLIB2Whitespace

type internal Z3Parser() =
    let smt2libcommonparser = new SMTCommonParser()
    let smt2liboutputparser = new SMTOutputParser()
        
    let parsePrecisionIntern =
        let parsePrecise = str "precise"        >>% Precision.PrecisionPrecise
        let parseUnder = str "under"            >>% Precision.PrecisionUnder
        let parseOver = str "over"              >>% Precision.PrecisionOver
        let parseUnderOver = str "under-over"   >>% Precision.PrecisionUnderOver
        str ":precision" >>. smt2ws >>. choice [parsePrecise;parseUnder;parseOver;parseUnderOver]

    let parseDepthIntern =
        str ":depth" >>. smt2ws >>. pint32

    let parseExprIntern = smt2libcommonparser.parseTerm
    
    // TODO (incomplete): GoalDependency contains for every Expr in Goals its dependencies and the definitions (display_with_dependencies in z3/src/tactic/goal.cpp)
    //let parseGoalDependencyEntryIntern =

    //TODO
    //let parseGoalDependencyIntern =

    let parseGoalIntern : Parser<Goal,unit> =
        let parseGoalWithGoalDependency = 
            preturn None //TODO
        let parseGoalWithoutGoalDependency = 
            let parseExprListOfGoal = many parseExprIntern
            let parseGoalDependency = preturn None //TODO :
            let parseFrameOfGoal innerparser =
                smt2ws >>. str "(" >>. smt2ws >>. str "goal" >>. smt2ws >>. innerparser .>> smt2ws .>> str ")" .>> smt2ws
            parseFrameOfGoal 
                (tuple4 (parseExprListOfGoal .>>smt2ws) (parsePrecisionIntern .>>smt2ws) (parseDepthIntern .>>smt2ws) (parseGoalDependency .>>smt2ws))
        parseGoalWithoutGoalDependency    

    let parseGoalsIntern =
        let parseFrameOfGoals innerparser =
            smt2ws >>. str "(" >>. smt2ws >>. str "goals" >>. smt2ws >>. innerparser .>> smt2ws .>> str ")" .>> smt2ws
        parseFrameOfGoals (many parseGoalIntern)

    // Members of Type
    member this.parsePrecision           : Parser<_,unit> = parsePrecisionIntern
    member this.parseDepth               : Parser<_,unit> = parseDepthIntern
    member this.parseExpr                : Parser<_,unit> = parseExprIntern
    //member this.parseGoalDependencyEntry : Parser<_,unit> = parseGoalDependencyEntryIntern
    //member this.parseGoalDependency      : Parser<_,unit> = parseGoalDependencyIntern
    member this.parseGoal                : Parser<_,unit> = parseGoalIntern
    member this.parseGoals               : Parser<_,unit> = parseGoalsIntern