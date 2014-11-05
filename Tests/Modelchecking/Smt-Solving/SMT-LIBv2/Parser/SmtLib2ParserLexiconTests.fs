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
open SMTLIB2Parser
open SMTLIB2DataStructures.Ast
open AstTestHelpers
open SmtLib2ParsingResult

type SMTLexiconExampleTests() =
    let parser = new SMTCommonParser()
    
    let inAstFloat         = inAst<float>
    let inAstNumeral       = inAst<Numeral>
    let inAstDecimal       = inAst<Decimal>
    let inAstHexadecimal   = inAst<Hexadecimal>
    let inAstBinary        = inAst<Binary>
    let inAstString        = inAst<String>
    let inAstReservedWords = inAst<ReservedWords>
    let inAstSymbol        = inAst<Symbol>
    let inAstKeyword       = inAst<Keyword>

    let parseWithParser parser str =
        match run parser str with
        | Success(result, _, _)   -> (Ast result)
        | Failure(errorMsg, _, _) -> (Error errorMsg)
        
    let parseFloat str        = parseWithParser (pfloat .>> eof) str
    let parseNumeral str      = parseWithParser (parser.parseNumeral .>> eof) str
    let parseDecimal str      = parseWithParser (parser.parseDecimal .>> eof) str
    let parseHexadecimal str  = parseWithParser (parser.parseHexadecimal .>> eof) str
    let parseBinary str       = parseWithParser (parser.parseBinary .>> eof) str
    let parseString str       = parseWithParser (parser.parseString .>> eof) str
    let parseReservedWord str = parseWithParser (parser.parseReservedWord .>> eof) str
    let parseSymbol str       = parseWithParser (parser.parseSymbol .>> eof) str
    let parseKeyword str      = parseWithParser (parser.parseKeyword .>> eof) str
                 
    [<Test>]
    member this.``Datastructure ParsingResult works with convenience function returnAstFloat``() =
        (ParsingResult<float>.Ast 1.25) =? inAstFloat 1.25

    [<Test>]
    member this.``a simple float should parse correctly``() =
        parseFloat "1.25" =? inAstFloat 1.25


        
    [<Test>]
    member this.``a numeral like '1' should parse correctly``() =
        parseNumeral "1" =? inAstNumeral (System.Numerics.BigInteger(1))
        
    [<Test>]
    member this.``a numeral like '0' should parse correctly``() =
        parseNumeral "0" =? inAstNumeral (System.Numerics.BigInteger(0))
        
    [<Test>]
    member this.``a string like '01' cannot be parsed as numeral``() =
        parseNumeral "01" |> failsParsing

                
    [<Test>]
    member this.``a decimal like '1.01' should parse correctly``() =
        parseDecimal "1.25" =? inAstDecimal "1.25"
        
    [<Test>]
    member this.``a decimal like '2.1' should parse correctly``() =
        parseDecimal "2.1" =? inAstDecimal "2.1"

    [<Test>]
    member this.``a decimal like '0.0' should parse correctly``() =
        parseDecimal "0.0" =? inAstDecimal "0.0"
        
    [<Test>]
    member this.``a decimal like '0.1' should parse correctly``() =
        parseDecimal "0.1" =? inAstDecimal "0.1"

    [<Test>]
    member this.``a decimal like '1.0' should parse correctly``() =
        parseDecimal "1.0" =? inAstDecimal "1.0"
        
    [<Test>]
    member this.``a decimal like '1.001' should parse correctly``() =
        parseDecimal "1.001" =? inAstDecimal "1.001"
                
    [<Test>]
    member this.``a decimal like '1.000' should parse correctly``() =
        parseDecimal "1.000" =? inAstDecimal "1.000"

    [<Test>]
    member this.``a decimal like '1.010' should parse correctly``() =
        parseDecimal "1.010" =? inAstDecimal "1.010"

    [<Test>]
    member this.``a string like '00.0' cannot be parsed as decimal``() =
        parseDecimal "00.0" |> failsParsing

        
    [<Test>]
    member this.``a hexadecimal like '#x0' should parse correctly``() =
        parseHexadecimal "#x0" =? inAstHexadecimal "#x0"

    [<Test>]
    member this.``a hexadecimal like '#x01Ab' should parse correctly``() =
        parseHexadecimal "#x01Ab" =? inAstHexadecimal "#x01Ab"

    [<Test>]
    member this.``a hexadecimal like '#xA04' should parse correctly``() =
        parseHexadecimal "#xA04" =? inAstHexadecimal "#xA04"

    [<Test>]
    member this.``a hexadecimal like '#x61ff' should parse correctly``() =
        parseHexadecimal "#x61ff" =? inAstHexadecimal "#x61ff"


    [<Test>]
    member this.``a binary like '#b0' should parse correctly``() =
        parseBinary "#b0" =? inAstBinary "#b0"

    [<Test>]
    member this.``a binary like '#b1' should parse correctly``() =
        parseBinary "#b1" =? inAstBinary "#b1"

    [<Test>]
    member this.``a binary like '#b001' should parse correctly``() =
        parseBinary "#b001" =? inAstBinary "#b001"

    [<Test>]
    member this.``a binary like '#b101011' should parse correctly``() =
        parseBinary "#b101011" =? inAstBinary "#b101011"
        
        
    [<Test>]
    member this.``an empty string should parse correctly``() =
        parseString "\"\"" =? inAstString ""

    [<Test>]
    member this.``a simple string should parse correctly``() =
        parseString "\"this is a string literal\"" =? inAstString "this is a string literal"
        
    [<Test>]
    member this.``a string with a backslash should parse correctly``() =
        parseString "\"Here is a backslash: \\\\\"" =? inAstString "Here is a backslash: \\"
        
    [<Test>]
    member this.``a string with a quote should parse correctly``() =
        parseString "\"She said: \\\"Hello!\\\"\"" =? inAstString "She said: \"Hello!\""
        
    [<Test>]
    member this.``a string with a backslash only escapes on backslashes and quotes, not on 't'``() =
        parseString "\"\\t\"" =? inAstString "\\t"
        
    [<Test>]
    member this.``a string with a backslash only escapes on backslashes and quotes, not on 'n'(newline)``() =
        parseString "\"one\\n two\"" =? inAstString "one\\n two"

    [<Test>]
    member this.``reserved words like 'par' parse correctly``() =
        parseReservedWord "par" =? inAstReservedWords ReservedWords.ReservedWord_par

    [<Test>]
    member this.``reserved words like 'NUMERAL' parse correctly``() =
        parseReservedWord "NUMERAL" =? inAstReservedWords ReservedWords.ReservedWord_NUMERAL

    [<Test>]
    member this.``reserved words like 'DECIMAL' parse correctly``() =
        parseReservedWord "DECIMAL" =? inAstReservedWords ReservedWords.ReservedWord_DECIMAL

    [<Test>]
    member this.``reserved words like 'STRING' parse correctly``() =
        parseReservedWord "STRING" =? inAstReservedWords ReservedWords.ReservedWord_STRING

    [<Test>]
    member this.``reserved words like '_' parse correctly``() =
        parseReservedWord "_" =? inAstReservedWords ReservedWords.ReservedWord_Underscore

    [<Test>]
    member this.``reserved words like '!' parse correctly``() =
        parseReservedWord "!" =? inAstReservedWords ReservedWords.ReservedWord_ExclamationMark

    [<Test>]
    member this.``reserved words like 'as' parse correctly``() =
        parseReservedWord "as" =? inAstReservedWords ReservedWords.ReservedWord_as

    [<Test>]
    member this.``reserved words like 'let' parse correctly``() =
        parseReservedWord "let" =? inAstReservedWords ReservedWords.ReservedWord_let

    [<Test>]
    member this.``reserved words like 'forall' parse correctly``() =
        parseReservedWord "forall" =? inAstReservedWords ReservedWords.ReservedWord_forall

    [<Test>]
    member this.``reserved words like 'exists' parse correctly``() =
        parseReservedWord "exists" =? inAstReservedWords ReservedWords.ReservedWord_exists
        
        
    [<Test>]
    member this.``a simple symbol like '+' parse correctly``() =
        parseSymbol "+" =? inAstSymbol (Symbol("+"))

    [<Test>]
    member this.``a simple symbol like '<=' parse correctly``() =
        parseSymbol "<=" =? inAstSymbol (Symbol("<="))

    [<Test>]
    member this.``a simple symbol like 'x' parse correctly``() =
        parseSymbol "x" =? inAstSymbol (Symbol("x"))

    [<Test>]
    member this.``a simple symbol like 'plus' parse correctly``() =
        parseSymbol "plus" =? inAstSymbol (Symbol("plus"))

    [<Test>]
    member this.``a simple symbol like '**' parse correctly``() =
        parseSymbol "**" =? inAstSymbol (Symbol("**"))

    [<Test>]
    member this.``a simple symbol like '$' parse correctly``() =
        parseSymbol "$" =? inAstSymbol (Symbol("$"))

    [<Test>]
    member this.``a simple symbol like '<sas' parse correctly``() =
        parseSymbol "<sas" =? inAstSymbol (Symbol("<sas"))
        
    [<Test>]
    member this.``a simple symbol like '<adf>' parse correctly``() =
        parseSymbol "<adf>" =? inAstSymbol (Symbol("<adf>"))

    [<Test>]
    member this.``a simple symbol like 'abc77' parse correctly``() =
        parseSymbol "abc77" =? inAstSymbol (Symbol("abc77"))

    [<Test>]
    member this.``a simple symbol like '*$s&6' parse correctly``() =
        parseSymbol "*$s&6" =? inAstSymbol (Symbol("*$s&6"))

    [<Test>]
    member this.``a simple symbol like '.kkk' parse correctly``() =
        parseSymbol ".kkk" =? inAstSymbol (Symbol(".kkk"))

    [<Test>]
    member this.``a simple symbol like '.8' parse correctly``() =
        parseSymbol ".8" =? inAstSymbol (Symbol(".8"))

    [<Test>]
    member this.``a simple symbol like '+34' parse correctly``() =
        parseSymbol "+34" =? inAstSymbol (Symbol("+34"))

    [<Test>]
    member this.``a simple symbol like '-32' parse correctly``() =
        parseSymbol "-32" =? inAstSymbol (Symbol("-32"))

        
    [<Test>]
    member this.``a quoted symbol like '|this is a single quoted symbol|' should parse correctly``() =
        parseSymbol "|this is a single quoted symbol|" =? inAstSymbol (Symbol("this is a single quoted symbol"))

    [<Test>]
    member this.``a quoted symbol like '||' should parse correctly``() =
        parseSymbol "||" =? inAstSymbol (Symbol(""))

    [<Test>]
    member this.``a quoted symbol with many special characters should parse correctly``() =
        parseSymbol "|af klj^*(0asfsfe2(&*)&(#^$>>>?\"']]984|" =? inAstSymbol (Symbol("af klj^*(0asfsfe2(&*)&(#^$>>>?\"']]984"))
        

    [<Test>]
    member this.``a keyword like ':date' should parse correctly``() =
        parseKeyword ":date" =? inAstKeyword (Keyword("date"))

    [<Test>]
    member this.``a keyword like ':a2' should parse correctly``() =
        parseKeyword ":a2" =? inAstKeyword (Keyword("a2"))

    [<Test>]
    member this.``a keyword like ':foo-bar' should parse correctly``() =
        parseKeyword ":foo-bar" =? inAstKeyword (Keyword("foo-bar"))

    [<Test>]
    member this.``a keyword like ':<=' should parse correctly``() =
        parseKeyword ":<=" =? inAstKeyword (Keyword("<="))

    [<Test>]
    member this.``a keyword like ':56' should parse correctly``() =
        parseKeyword ":56" =? inAstKeyword (Keyword("56"))

    [<Test>]
    member this.``a keyword like ':->' should parse correctly``() =
        parseKeyword ":->" =? inAstKeyword (Keyword("->"))
    