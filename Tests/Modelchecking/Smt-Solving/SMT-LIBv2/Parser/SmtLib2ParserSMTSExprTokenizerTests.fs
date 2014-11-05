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
open SmtLib2ParsingResult

type SMTSExprTokenizerExampleTests() =
    // returns, whether the tokenizer finishes or not
    let tokenize str : bool =
        let tokenizer = new SMTSExpressionTokenizer()
        tokenizer.ParseNewInput (str + "\n")

    [<Test>]
    member this.``a numeral like '1' should be tokenized correctly``() =
        tokenize "1" =? true
        
    [<Test>]
    member this.``a numeral like '0' should be tokenized correctly``() =
        tokenize "0" =? true
        
    [<Test>]
    member this.``a string like '01' cannot be parsed as numeral``() =
        tokenize "01" =? true

                
    [<Test>]
    member this.``a decimal like '1.01' should be tokenized correctly``() =
        tokenize "1.25" =? true
        
    [<Test>]
    member this.``a decimal like '2.1' should be tokenized correctly``() =
        tokenize "2.1" =? true

    [<Test>]
    member this.``a decimal like '0.0' should be tokenized correctly``() =
        tokenize "0.0" =? true
        
    [<Test>]
    member this.``a decimal like '0.1' should be tokenized correctly``() =
        tokenize "0.1" =? true

    [<Test>]
    member this.``a decimal like '1.0' should be tokenized correctly``() =
        tokenize "1.0" =? true
        
    [<Test>]
    member this.``a decimal like '1.001' should be tokenized correctly``() =
        tokenize "1.001" =? true
                
    [<Test>]
    member this.``a decimal like '1.000' should be tokenized correctly``() =
        tokenize "1.000" =? true

    [<Test>]
    member this.``a decimal like '1.010' should be tokenized correctly``() =
        tokenize "1.010" =? true

    [<Test>]
    member this.``a string like '00.0' cannot be parsed as decimal``() =
        tokenize "00.0" =? true

        
    [<Test>]
    member this.``a hexadecimal like '#x0' should be tokenized correctly``() =
        tokenize "#x0" =? true

    [<Test>]
    member this.``a hexadecimal like '#x01Ab' should be tokenized correctly``() =
        tokenize "#x01Ab" =? true

    [<Test>]
    member this.``a hexadecimal like '#xA04' should be tokenized correctly``() =
        tokenize "#xA04" =? true

    [<Test>]
    member this.``a hexadecimal like '#x61ff' should be tokenized correctly``() =
        tokenize "#x61ff" =? true


    [<Test>]
    member this.``a binary like '#b0' should be tokenized correctly``() =
        tokenize "#b0" =? true

    [<Test>]
    member this.``a binary like '#b1' should be tokenized correctly``() =
        tokenize "#b1" =? true

    [<Test>]
    member this.``a binary like '#b001' should be tokenized correctly``() =
        tokenize "#b001" =? true

    [<Test>]
    member this.``a binary like '#b101011' should be tokenized correctly``() =
        tokenize "#b101011" =? true
        
        
    [<Test>]
    member this.``an empty string should be tokenized correctly``() =
        tokenize "\"\"" =? true

    [<Test>]
    member this.``a simple string should be tokenized correctly``() =
        tokenize "\"this is a string literal\"" =? true
        
    [<Test>]
    member this.``a string with a backslash should be tokenized correctly``() =
        tokenize "\"Here is a backslash: \\\\\"" =? true
        
    [<Test>]
    member this.``a string with a quote should be tokenized correctly``() =
        tokenize "\"She said: \\\"Hello!\\\"\"" =? true
        
    [<Test>]
    member this.``a string with a backslash only escapes on backslashes and quotes, not on 't'``() =
        tokenize "\"\\t\"" =? true
        
    [<Test>]
    member this.``a string with a backslash only escapes on backslashes and quotes, not on 'n'(newline)``() =
        tokenize "\"one\\n two\"" =? true

    [<Test>]
    member this.``a simple symbol like '+' parse correctly``() =
        tokenize "+" =? true

    [<Test>]
    member this.``a simple symbol like '<=' parse correctly``() =
        tokenize "<=" =? true

    [<Test>]
    member this.``a simple symbol like 'x' parse correctly``() =
        tokenize "x" =? true

    [<Test>]
    member this.``a simple symbol like 'plus' parse correctly``() =
        tokenize "plus" =? true

    [<Test>]
    member this.``a simple symbol like '**' parse correctly``() =
        tokenize "**" =? true

    [<Test>]
    member this.``a simple symbol like '$' parse correctly``() =
        tokenize "$" =? true

    [<Test>]
    member this.``a simple symbol like '<sas' parse correctly``() =
        tokenize "<sas" =? true
        
    [<Test>]
    member this.``a simple symbol like '<adf>' parse correctly``() =
        tokenize "<adf>" =? true

    [<Test>]
    member this.``a simple symbol like 'abc77' parse correctly``() =
        tokenize "abc77" =? true

    [<Test>]
    member this.``a simple symbol like '*$s&6' parse correctly``() =
        tokenize "*$s&6" =? true

    [<Test>]
    member this.``a simple symbol like '.kkk' parse correctly``() =
        tokenize ".kkk" =? true

    [<Test>]
    member this.``a simple symbol like '.8' parse correctly``() =
        tokenize ".8" =? true

    [<Test>]
    member this.``a simple symbol like '+34' parse correctly``() =
        tokenize "+34" =? true

    [<Test>]
    member this.``a simple symbol like '-32' parse correctly``() =
        tokenize "-32" =? true

        
    [<Test>]
    member this.``a quoted symbol like '|this is a single quoted symbol|' should be tokenized correctly``() =
        tokenize "|this is a single quoted symbol|" =? true

    [<Test>]
    member this.``a quoted symbol like '||' should be tokenized correctly``() =
        tokenize "||" =? true

    [<Test>]
    member this.``a quoted symbol with many special characters should be tokenized correctly``() =
        tokenize "|af klj^*(0asfsfe2(&*)&(#^$>>>?\"']]984|" =? true
        

    [<Test>]
    member this.``a keyword like ':date' should be tokenized correctly``() =
        tokenize ":date" =? true

    [<Test>]
    member this.``a keyword like ':a2' should be tokenized correctly``() =
        tokenize ":a2" =? true

    [<Test>]
    member this.``a keyword like ':foo-bar' should be tokenized correctly``() =
        tokenize ":foo-bar" =? true

    [<Test>]
    member this.``a keyword like ':<=' should be tokenized correctly``() =
        tokenize ":<=" =? true

    [<Test>]
    member this.``a keyword like ':56' should be tokenized correctly``() =
        tokenize ":56" =? true

    [<Test>]
    member this.``a keyword like ':->' should be tokenized correctly``() =
        tokenize ":->" =? true

        
    [<Test>]
    member this.``a sexpr-list like '( p x0 a )' should be tokenized correctly``() =
        let a = tokenize "( p )"
        tokenize "( p x0 a )" =? true
        