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

type SMTSpecConstantExampleTests() =
    let parser = new SMTCommonParser()
    
    let inAstFloat         = inAst<float>
    let inAstSpecConstant  = inAst<SpecConstant>

    let parseWithParser parser str =
        match run parser str with
        | Success(result, _, _)   -> (Ast result)
        | Failure(errorMsg, _, _) -> (Error errorMsg)
        
    let parseFloat str        = parseWithParser pfloat str
    let parseSpecConstant str      = parseWithParser (parser.parseSpecConstant .>> eof) str
                 
    [<Test>]
    member this.``Datastructure ParsingResult works with convenience function returnAstFloat``() =
        (ParsingResult<float>.Ast 1.25) =? inAstFloat 1.25

    [<Test>]
    member this.``a simple float should parse correctly``() =
        parseFloat "1.25" =? inAstFloat 1.25


    [<Test>]
    member this.``a numeral like '1' should parse correctly``() =
        parseSpecConstant "1" =? inAstSpecConstant (SpecConstant.SpecConstantNumeral(System.Numerics.BigInteger(1)))
        
    [<Test>]
    member this.``a numeral like '0' should parse correctly``() =
        parseSpecConstant "0" =? inAstSpecConstant (SpecConstant.SpecConstantNumeral(System.Numerics.BigInteger(0)))
        
    [<Test>]
    member this.``a string like '01' cannot be parsed as numeral``() =
        parseSpecConstant "01" |> failsParsing

                
    [<Test>]
    member this.``a decimal like '1.01' should parse correctly``() =
        parseSpecConstant "1.25" =? inAstSpecConstant (SpecConstant.SpecConstantDecimal("1.25"))
        
    [<Test>]
    member this.``a decimal like '2.1' should parse correctly``() =
        parseSpecConstant "2.1" =? inAstSpecConstant (SpecConstant.SpecConstantDecimal("2.1"))

    [<Test>]
    member this.``a decimal like '0.0' should parse correctly``() =
        parseSpecConstant "0.0" =? inAstSpecConstant (SpecConstant.SpecConstantDecimal("0.0"))
        
    [<Test>]
    member this.``a decimal like '0.1' should parse correctly``() =
        parseSpecConstant "0.1" =? inAstSpecConstant (SpecConstant.SpecConstantDecimal("0.1"))

    [<Test>]
    member this.``a decimal like '1.0' should parse correctly``() =
        parseSpecConstant "1.0" =? inAstSpecConstant (SpecConstant.SpecConstantDecimal("1.0"))
        
    [<Test>]
    member this.``a decimal like '1.001' should parse correctly``() =
        parseSpecConstant "1.001" =? inAstSpecConstant (SpecConstant.SpecConstantDecimal("1.001"))
                
    [<Test>]
    member this.``a decimal like '1.000' should parse correctly``() =
        parseSpecConstant "1.000" =? inAstSpecConstant (SpecConstant.SpecConstantDecimal("1.000"))

    [<Test>]
    member this.``a decimal like '1.010' should parse correctly``() =
        parseSpecConstant "1.010" =? inAstSpecConstant (SpecConstant.SpecConstantDecimal("1.010"))

    [<Test>]
    member this.``a string like '00.0' cannot be parsed as decimal``() =
        parseSpecConstant "00.0" |> failsParsing

        
    [<Test>]
    member this.``a hexadecimal like '#x0' should parse correctly``() =
        parseSpecConstant "#x0" =? inAstSpecConstant (SpecConstant.SpecConstantHexadecimal("#x0"))

    [<Test>]
    member this.``a hexadecimal like '#x01Ab' should parse correctly``() =
        parseSpecConstant "#x01Ab" =? inAstSpecConstant (SpecConstant.SpecConstantHexadecimal("#x01Ab"))

    [<Test>]
    member this.``a hexadecimal like '#xA04' should parse correctly``() =
        parseSpecConstant "#xA04" =? inAstSpecConstant (SpecConstant.SpecConstantHexadecimal("#xA04"))

    [<Test>]
    member this.``a hexadecimal like '#x61ff' should parse correctly``() =
        parseSpecConstant "#x61ff" =? inAstSpecConstant (SpecConstant.SpecConstantHexadecimal("#x61ff"))


    [<Test>]
    member this.``a binary like '#b0' should parse correctly``() =
        parseSpecConstant "#b0" =? inAstSpecConstant (SpecConstant.SpecConstantBinary("#b0"))

    [<Test>]
    member this.``a binary like '#b1' should parse correctly``() =
        parseSpecConstant "#b1" =? inAstSpecConstant (SpecConstant.SpecConstantBinary("#b1"))

    [<Test>]
    member this.``a binary like '#b001' should parse correctly``() =
        parseSpecConstant "#b001" =? inAstSpecConstant (SpecConstant.SpecConstantBinary("#b001"))

    [<Test>]
    member this.``a binary like '#b101011' should parse correctly``() =
        parseSpecConstant "#b101011" =? inAstSpecConstant (SpecConstant.SpecConstantBinary("#b101011"))
        
        
    [<Test>]
    member this.``an empty string should parse correctly``() =
        parseSpecConstant "\"\"" =? inAstSpecConstant (SpecConstant.SpecConstantString(""))

    [<Test>]
    member this.``a simple string should parse correctly``() =
        parseSpecConstant "\"this is a string literal\"" =? inAstSpecConstant (SpecConstant.SpecConstantString("this is a string literal"))
        
    [<Test>]
    member this.``a string with a backslash should parse correctly``() =
        parseSpecConstant "\"Here is a backslash: \\\\\"" =? inAstSpecConstant (SpecConstant.SpecConstantString("Here is a backslash: \\"))
        
    [<Test>]
    member this.``a string with a quote should parse correctly``() =
        parseSpecConstant "\"She said: \\\"Hello!\\\"\"" =? inAstSpecConstant (SpecConstant.SpecConstantString("She said: \"Hello!\""))
        
    [<Test>]
    member this.``a string with a backslash only escapes on backslashes and quotes, not on 't'``() =
        parseSpecConstant "\"\\t\"" =? inAstSpecConstant (SpecConstant.SpecConstantString("\\t"))
        
    [<Test>]
    member this.``a string with a backslash only escapes on backslashes and quotes, not on 'n'(newline)``() =
        parseSpecConstant "\"one\\n two\"" =? inAstSpecConstant (SpecConstant.SpecConstantString("one\\n two"))