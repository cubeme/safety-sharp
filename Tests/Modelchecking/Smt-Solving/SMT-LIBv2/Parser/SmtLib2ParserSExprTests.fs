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

namespace SMTLIB2Parser.Tests

open System
open NUnit.Framework
open FParsec

open TestHelpers
open AstTestHelpers
open SafetySharp.Internal.SmtSolving.SmtLib2.Ast
open SafetySharp.Internal.SmtSolving.SmtLib2.Parser
open SafetySharp.Internal.SmtSolving.SmtLib2.Parser.SmtLib2ParsingResult

type SMTSExprExampleTests() =
    let parser = new SMTCommonParser()
    
    let inAstFloat  = inAst<float>
    let inAstSExpr  = inAst<SExpr>

    let parseWithParser parser str =
        match run parser str with
        | Success(result, _, _)   -> (Ast result)
        | Failure(errorMsg, _, _) -> (Error errorMsg)
        
    let parseFloat str        = parseWithParser pfloat str
    let parseSExpr str      = parseWithParser (parser.parseSExpr .>> eof) str
                 
    [<Test>]
    member this.``Datastructure ParsingResult works with convenience function returnAstFloat``() =
        (ParsingResult<float>.Ast 1.25) =? inAstFloat 1.25

    [<Test>]
    member this.``a simple float should parse correctly``() =
        parseFloat "1.25" =? inAstFloat 1.25


    [<Test>]
    member this.``a numeral like '1' should parse correctly``() =
        parseSExpr "1" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantNumeral(System.Numerics.BigInteger(1))))
        
    [<Test>]
    member this.``a numeral like '0' should parse correctly``() =
        parseSExpr "0" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantNumeral(System.Numerics.BigInteger(0))))
        
    [<Test>]
    member this.``a string like '01' cannot be parsed as numeral``() =
        parseSExpr "01" |> failsParsing

                
    [<Test>]
    member this.``a decimal like '1.01' should parse correctly``() =
        parseSExpr "1.25" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantDecimal("1.25")))
        
    [<Test>]
    member this.``a decimal like '2.1' should parse correctly``() =
        parseSExpr "2.1" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantDecimal("2.1")))

    [<Test>]
    member this.``a decimal like '0.0' should parse correctly``() =
        parseSExpr "0.0" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantDecimal("0.0")))
        
    [<Test>]
    member this.``a decimal like '0.1' should parse correctly``() =
        parseSExpr "0.1" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantDecimal("0.1")))

    [<Test>]
    member this.``a decimal like '1.0' should parse correctly``() =
        parseSExpr "1.0" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantDecimal("1.0")))
        
    [<Test>]
    member this.``a decimal like '1.001' should parse correctly``() =
        parseSExpr "1.001" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantDecimal("1.001")))
                
    [<Test>]
    member this.``a decimal like '1.000' should parse correctly``() =
        parseSExpr "1.000" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantDecimal("1.000")))

    [<Test>]
    member this.``a decimal like '1.010' should parse correctly``() =
        parseSExpr "1.010" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantDecimal("1.010")))

    [<Test>]
    member this.``a string like '00.0' cannot be parsed as decimal``() =
        parseSExpr "00.0" |> failsParsing

        
    [<Test>]
    member this.``a hexadecimal like '#x0' should parse correctly``() =
        parseSExpr "#x0" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantHexadecimal("#x0")))

    [<Test>]
    member this.``a hexadecimal like '#x01Ab' should parse correctly``() =
        parseSExpr "#x01Ab" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantHexadecimal("#x01Ab")))

    [<Test>]
    member this.``a hexadecimal like '#xA04' should parse correctly``() =
        parseSExpr "#xA04" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantHexadecimal("#xA04")))

    [<Test>]
    member this.``a hexadecimal like '#x61ff' should parse correctly``() =
        parseSExpr "#x61ff" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantHexadecimal("#x61ff")))


    [<Test>]
    member this.``a binary like '#b0' should parse correctly``() =
        parseSExpr "#b0" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantBinary("#b0")))

    [<Test>]
    member this.``a binary like '#b1' should parse correctly``() =
        parseSExpr "#b1" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantBinary("#b1")))

    [<Test>]
    member this.``a binary like '#b001' should parse correctly``() =
        parseSExpr "#b001" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantBinary("#b001")))

    [<Test>]
    member this.``a binary like '#b101011' should parse correctly``() =
        parseSExpr "#b101011" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantBinary("#b101011")))
        
        
    [<Test>]
    member this.``an empty string should parse correctly``() =
        parseSExpr "\"\"" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantString("")))

    [<Test>]
    member this.``a simple string should parse correctly``() =
        parseSExpr "\"this is a string literal\"" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantString("this is a string literal")))
        
    [<Test>]
    member this.``a string with a backslash should parse correctly``() =
        parseSExpr "\"Here is a backslash: \\\\\"" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantString("Here is a backslash: \\")))
        
    [<Test>]
    member this.``a string with a quote should parse correctly``() =
        parseSExpr "\"She said: \\\"Hello!\\\"\"" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantString("She said: \"Hello!\"")))
        
    [<Test>]
    member this.``a string with a backslash only escapes on backslashes and quotes, not on 't'``() =
        parseSExpr "\"\\t\"" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantString("\\t")))
        
    [<Test>]
    member this.``a string with a backslash only escapes on backslashes and quotes, not on 'n'(newline)``() =
        parseSExpr "\"one\\n two\"" =? inAstSExpr (SExpr.SExprSpecConstant(SpecConstant.SpecConstantString("one\\n two")))

    [<Test>]
    member this.``a simple symbol like '+' parse correctly``() =
        parseSExpr "+" =? inAstSExpr (SExpr.SExprSymbol(Symbol("+")))

    [<Test>]
    member this.``a simple symbol like '<=' parse correctly``() =
        parseSExpr "<=" =? inAstSExpr (SExpr.SExprSymbol(Symbol("<=")))

    [<Test>]
    member this.``a simple symbol like 'x' parse correctly``() =
        parseSExpr "x" =? inAstSExpr (SExpr.SExprSymbol(Symbol("x")))

    [<Test>]
    member this.``a simple symbol like 'plus' parse correctly``() =
        parseSExpr "plus" =? inAstSExpr (SExpr.SExprSymbol(Symbol("plus")))

    [<Test>]
    member this.``a simple symbol like '**' parse correctly``() =
        parseSExpr "**" =? inAstSExpr (SExpr.SExprSymbol(Symbol("**")))

    [<Test>]
    member this.``a simple symbol like '$' parse correctly``() =
        parseSExpr "$" =? inAstSExpr (SExpr.SExprSymbol(Symbol("$")))

    [<Test>]
    member this.``a simple symbol like '<sas' parse correctly``() =
        parseSExpr "<sas" =? inAstSExpr (SExpr.SExprSymbol(Symbol("<sas")))
        
    [<Test>]
    member this.``a simple symbol like '<adf>' parse correctly``() =
        parseSExpr "<adf>" =? inAstSExpr (SExpr.SExprSymbol(Symbol("<adf>")))

    [<Test>]
    member this.``a simple symbol like 'abc77' parse correctly``() =
        parseSExpr "abc77" =? inAstSExpr (SExpr.SExprSymbol(Symbol("abc77")))

    [<Test>]
    member this.``a simple symbol like '*$s&6' parse correctly``() =
        parseSExpr "*$s&6" =? inAstSExpr (SExpr.SExprSymbol(Symbol("*$s&6")))

    [<Test>]
    member this.``a simple symbol like '.kkk' parse correctly``() =
        parseSExpr ".kkk" =? inAstSExpr (SExpr.SExprSymbol(Symbol(".kkk")))

    [<Test>]
    member this.``a simple symbol like '.8' parse correctly``() =
        parseSExpr ".8" =? inAstSExpr (SExpr.SExprSymbol(Symbol(".8")))

    [<Test>]
    member this.``a simple symbol like '+34' parse correctly``() =
        parseSExpr "+34" =? inAstSExpr (SExpr.SExprSymbol(Symbol("+34")))

    [<Test>]
    member this.``a simple symbol like '-32' parse correctly``() =
        parseSExpr "-32" =? inAstSExpr (SExpr.SExprSymbol(Symbol("-32")))

        
    [<Test>]
    member this.``a quoted symbol like '|this is a single quoted symbol|' should parse correctly``() =
        parseSExpr "|this is a single quoted symbol|" =? inAstSExpr (SExpr.SExprSymbol(Symbol("this is a single quoted symbol")))

    [<Test>]
    member this.``a quoted symbol like '||' should parse correctly``() =
        parseSExpr "||" =? inAstSExpr (SExpr.SExprSymbol(Symbol("")))

    [<Test>]
    member this.``a quoted symbol with many special characters should parse correctly``() =
        parseSExpr "|af klj^*(0asfsfe2(&*)&(#^$>>>?\"']]984|" =? inAstSExpr (SExpr.SExprSymbol(Symbol("af klj^*(0asfsfe2(&*)&(#^$>>>?\"']]984")))
        

    [<Test>]
    member this.``a keyword like ':date' should parse correctly``() =
        parseSExpr ":date" =? inAstSExpr (SExpr.SExprKeyword(Keyword("date")))

    [<Test>]
    member this.``a keyword like ':a2' should parse correctly``() =
        parseSExpr ":a2" =? inAstSExpr (SExpr.SExprKeyword(Keyword("a2")))

    [<Test>]
    member this.``a keyword like ':foo-bar' should parse correctly``() =
        parseSExpr ":foo-bar" =? inAstSExpr (SExpr.SExprKeyword(Keyword("foo-bar")))

    [<Test>]
    member this.``a keyword like ':<=' should parse correctly``() =
        parseSExpr ":<=" =? inAstSExpr (SExpr.SExprKeyword(Keyword("<=")))

    [<Test>]
    member this.``a keyword like ':56' should parse correctly``() =
        parseSExpr ":56" =? inAstSExpr (SExpr.SExprKeyword(Keyword("56")))

    [<Test>]
    member this.``a keyword like ':->' should parse correctly``() =
        parseSExpr ":->" =? inAstSExpr (SExpr.SExprKeyword(Keyword("->")))

        
    [<Test>]
    member this.``a sexpr-list like '( p x0 a )' should parse correctly``() =
        let a = parseSExpr "( p )"
        parseSExpr "( p x0 a )" =? inAstSExpr (SExpr.SExprSExprList [SExpr.SExprSymbol(Symbol.Symbol("p"));SExpr.SExprSymbol(Symbol.Symbol("x0"));SExpr.SExprSymbol(Symbol.Symbol("a"))])
        