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

namespace SafetySharp.Analysis.SmtSolving.SmtLib2.Parser

module internal ParseSMTLIB2Whitespace =

    // here we have to take into account, that ';' introduces a comment

    open FParsec

    // parses multiple whitespaces (tab, space, newline, ...)
    let ws = spaces

    // parses (p (sep p)+)?
    let sepBy1 p sep = pipe2 p (opt (sep >>. sepBy p sep)) 
                             (fun head tail -> match tail with | None -> [head] | Some(tail') -> head :: tail')

    // parses the given string
    let symbol s = pstring s .>> ws

    // parses the given keyword s and returns r
    let keyword s r = stringReturn s r .>> ws

    // parses 32-bit (signed/unsigned) integers and passes it to f
    let integer_ws f = pint32 .>> ws |>> f

    // defines the allowed characters at the beginning of an identifier
    let isIdentifierFirstChar c = isLetter c || c = '_'
    // defines the allowed characters after the first character of an identifier
    let isIdentifierChar c = isLetter c || isDigit c || c = '_'

    let parseAll p = ws >>. p .>> eof

    let str s = pstring s

    let str_ws s = pstring s .>> ws

    let skipWs : Parser<_,unit> = ws |>> ignore



    let smt2ws : Parser<unit,unit>=
        let parseComment =
            pchar ';' >>. restOfLine true
        (attempt (spaces >>. parseComment >>. spaces)) <|> spaces

    let str_smt2ws s = pstring s .>> smt2ws