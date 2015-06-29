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

namespace SafetySharp

module GenericParsers =

    open FParsec

    let parseNumeralAsStringIntern<'u> : Parser<_,'u> = // (from smt2 parser)
        let nonzero =            
            let isNonZeroDigit (char:char) = char >= '1' && char <= '9'
            let isDigit (char:char) = char >= '0' && char <= '9'
            many1Satisfy2 isNonZeroDigit isDigit
        let zero = pstring "0"
        (nonzero <|> zero)

    let parseDecimal<'u> : Parser<_,'u> = // (from smt2 parser. slightly modified)
        let concat (str1,str2) = str1 + "." + str2
        let zero = pstring "0"
        let parseBeforePoint = parseNumeralAsStringIntern
        let parseAfterPoint =
            let isDigit (char:char) = char >= '0' && char <= '9'
            let parseDigits = many1Satisfy isDigit
            parseDigits
        attempt (parseBeforePoint .>>. (pstring "." >>. parseAfterPoint)) |>> concat
        
    let parseBigint<'u> : Parser<_,'u> =
        many1Satisfy isDigit |>> ( fun value -> (bigint.Parse value))

        
    let parseDecimal_ws<'u> : Parser<_,'u> = parseDecimal .>> spaces
    let parseBigint_ws<'u> : Parser<_,'u> = parseBigint .>> spaces

    let pComment<'us> : Parser<unit,'us> =
        pstring<'us> ("//") .>>. (restOfLine<'us> true) >>% ()
    
    let pCommentOrSpace<'us> =
        spaces1<'us> <|> pComment<'us>

    let spaces<'us> = skipMany<unit,'us> pCommentOrSpace<'us>
    let spaces1<'us> = skipMany1<unit,'us> pCommentOrSpace<'us>