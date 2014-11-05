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

namespace SMTLIB2Parser

open System
open System.IO
open FParsec
open SMTLIB2DataStructures.Ast
open ParseSMTLIB2Whitespace

type SMTCommonParser() =        
    // forward parser declarations
    let parseSExprIntern, parseSExprRefIntern = createParserForwardedToRef()
    let parseSortIntern, parseSortRefIntern = createParserForwardedToRef()
    let parseTermIntern, parseTermRefIntern = createParserForwardedToRef()

    let betweenPara x = between (str "(" >>. smt2ws) (str ")" >>. smt2ws) x


    // Parse 3.1 Lexicon
    let parseNumeralAsStringIntern =
        let nonzero =            
            let isNonZeroDigit (char:char) = char >= '1' && char <= '9'
            let isDigit (char:char) = char >= '0' && char <= '9'
            many1Satisfy2 isNonZeroDigit isDigit
        let zero = str "0"
        (nonzero <|> zero)
    
    let parseNumeralIntern =
        let toBigInteger value = bigint.Parse(value)
        parseNumeralAsStringIntern |>> toBigInteger

    let parseDecimalIntern = 
        let concat (str1,str2) = str1 + "." + str2
        let zero = str "0"
        let parseBeforePoint = parseNumeralAsStringIntern
        let parseAfterPoint =
            let isDigit (char:char) = char >= '0' && char <= '9'
            let parseDigits = many1Satisfy isDigit
            parseDigits
        parseBeforePoint .>>. (str "." >>. parseAfterPoint) |>> concat
    
    let parseHexadecimalIntern =
        let isHexChar (char:char) = (char >= '0' && char <= '9') || (char >= 'A' && char <= 'F') || (char >= 'a' && char <= 'f')
        let parseBeginning = str "#x"
        let parseContent = many1Satisfy isHexChar
        let concat (str1,str2) = str1+str2
        (parseBeginning .>>. parseContent) |>> concat

    let parseBinaryIntern =
        let isBinChar (char:char) = (char = '0' || char = '1')
        let parseBeginning = str "#b"
        let parseContent = many1Satisfy isBinChar
        let concat (str1,str2) = str1+str2
        (parseBeginning .>>. parseContent) |>> concat
        
    let parseStringIntern =
        // SMT-LIB parses escaped chars a bit different than other languages (only \ and " may be escaped)
        let normalCharSnippet = manySatisfy (fun c -> c <> '\\' && c <> '"')
        let parseEscapedCharacter = (anyOf "\\\"" |>> fun c -> string c)
        let parseRegularCharPrefixedWithBackslash = (anyChar |>> fun c -> "\\" + string c)
        let escapedChar = pstring "\\" >>. ( (attempt parseEscapedCharacter) <|> parseRegularCharPrefixedWithBackslash )
        between (pstring "\"") (pstring "\"")
            (stringsSepBy normalCharSnippet escapedChar) 

    let parseReservedWordIntern =
                (pstring "par"     >>% ReservedWords.ReservedWord_par)
            <|> (pstring "NUMERAL" >>% ReservedWords.ReservedWord_NUMERAL)
            <|> (pstring "DECIMAL" >>% ReservedWords.ReservedWord_DECIMAL)
            <|> (pstring "STRING"  >>% ReservedWords.ReservedWord_STRING)
            <|> (pstring "_"       >>% ReservedWords.ReservedWord_Underscore)
            <|> (pstring "!"       >>% ReservedWords.ReservedWord_ExclamationMark)
            <|> (pstring "as"      >>% ReservedWords.ReservedWord_as)
            <|> (pstring "let"     >>% ReservedWords.ReservedWord_let)
            <|> (pstring "forall"  >>% ReservedWords.ReservedWord_forall)
            <|> (pstring "exists"  >>% ReservedWords.ReservedWord_exists)
    
    let isReservedWord str =
        match str with
            | "par"     -> true
            | "NUMERAL" -> true
            | "DECIMAL" -> true
            | "STRING" -> true
            | "_"       -> true
            | "!"       -> true
            | "as"      -> true
            | "let"     -> true
            | "forall"  -> true
            | "exists"  -> true
            | _ -> false

    let isAllowedSpecialCharacter char =
        match char with
            | '~' -> true
            | '!' -> true
            | '@' -> true
            | '$' -> true
            | '%' -> true
            | '^' -> true
            | '&' -> true
            | '*' -> true
            | '_' -> true
            | '-' -> true
            | '+' -> true
            | '=' -> true
            | '<' -> true
            | '>' -> true
            | '.' -> true
            | '?' -> true
            | '/' -> true
            | _ -> false

    let parseSymbolIntern =
        //let toSymbol str =
        //    if isReservedWord str <> true then Symbol.Symbol(str) else (fail "no reserved word expected")
        let parseSimpleSymbol =
            let beginningChar char =  isAsciiLetter char || isAllowedSpecialCharacter char
            let followingChars char = isAsciiLetter char || isAllowedSpecialCharacter char || isDigit char
            let uncheckedParser = identifier (IdentifierOptions(isAsciiIdStart = beginningChar, isAsciiIdContinue = followingChars)) |>> Symbol.Symbol
            (notFollowedBy parseReservedWordIntern >>. uncheckedParser)
        let parseQuotedSymbol =
            let parsePipe = (pstring "|")
            let isPipe char = char = '|'
            let isnotPipe char = not (isPipe char)
            between parsePipe parsePipe (notFollowedBy parseReservedWordIntern >>. (manySatisfy isnotPipe |>> Symbol.Symbol))
        parseSimpleSymbol <|> parseQuotedSymbol

    let parseKeywordIntern =
        let beginningChar char =  isAsciiLetter char || isAllowedSpecialCharacter char || isDigit char
        let followingChars char = isAsciiLetter char || isAllowedSpecialCharacter char || isDigit char
        pstring ":" >>. identifier (IdentifierOptions(isAsciiIdStart = beginningChar, isAsciiIdContinue = followingChars)) |>> Keyword.Keyword
    

    // Parse 3.2 S-expressions
    let parseDecoratedSExprIntern = betweenPara (many1 (parseSExprIntern .>> smt2ws))

    let parseSpecConstantIntern =
        choice [attempt parseDecimalIntern       |>> SpecConstant.SpecConstantDecimal;
                        parseNumeralIntern       |>> SpecConstant.SpecConstantNumeral;
                        parseHexadecimalIntern   |>> SpecConstant.SpecConstantHexadecimal;
                        parseBinaryIntern        |>> SpecConstant.SpecConstantBinary;
                        parseStringIntern        |>> SpecConstant.SpecConstantString
               ]
    
    do parseSExprRefIntern :=
        choice [ attempt parseSpecConstantIntern   |>> SExpr.SExprSpecConstant;
                 attempt parseSymbolIntern         |>> SExpr.SExprSymbol;
                 attempt parseKeywordIntern        |>> SExpr.SExprKeyword;
                         parseDecoratedSExprIntern |>> SExpr.SExprSExprList
               ]
    

    // Parse 3.3 Identifiers
    let parseIdentifierIntern =
        let parseIndexedIdentifier =
            betweenPara
                ((str "_" >>. smt2ws >>. parseSymbolIntern .>> smt2ws) .>>. many1 (parseNumeralIntern .>> smt2ws) |>> Identifier.IdIndexed)
        let parseCasualIdentifier =
            parseSymbolIntern |>> Identifier.IdSymbol
        parseIndexedIdentifier <|> parseCasualIdentifier
    

    // Parse 3.4 Attributes
    let parseAttributeValueIntern =
        choice [ attempt parseSpecConstantIntern |>> AttributeValue.AttributeValueSpecConstant;
                 attempt parseSymbolIntern       |>> AttributeValue.AttributeValueSymbol;
                 parseDecoratedSExprIntern       |>> AttributeValue.AttributeValueSExprList
               ]

    let parseAttributeIntern =
        let parseKeywordAttribute =
            parseKeywordIntern |>> Attribute.AttributeKeyword
        let parseKeywordWithValueAttribute =
            //betweenPara
                ((parseKeywordIntern .>> smt2ws) .>>. (parseAttributeValueIntern .>> smt2ws ) |>> Attribute.AttributeKeywordWithValue)
        (attempt parseKeywordWithValueAttribute) <|> parseKeywordAttribute


    // Parse 3.5 Sorts
    do parseSortRefIntern :=
        let parseSortSimple =
            parseIdentifierIntern |>> Sort.SortSimple
        let parseSortAdvanced =
            betweenPara
                ((parseIdentifierIntern .>> smt2ws) .>>. (many1 ( parseSortIntern .>> smt2ws )) |>> Sort.SortAdvanced)
        (attempt parseSortAdvanced) <|> parseSortSimple

    
    // Parse 3.6 Terms and Formulas
    let parseQualIdentifierIntern =
        let parseQualIdentifierOfSort =
            betweenPara
                ((str "as" >>. smt2ws >>. parseIdentifierIntern .>> smt2ws) .>>. (parseSortIntern .>> smt2ws) |>> QualIdentifierOfSort)
        let parseQualIdentifierSimple =
            parseIdentifierIntern |>> QualIdentifier.QualIdentifier
        parseQualIdentifierOfSort <|> parseQualIdentifierSimple
    
    let parseVarBindingIntern : Parser<VarBinding,unit> =
        betweenPara
            (parseSymbolIntern .>> smt2ws .>>. parseTermIntern .>> smt2ws)

    let parseSortedVarIntern : Parser<SortedVar,unit>=
        betweenPara
            (parseSymbolIntern .>> smt2ws .>>. parseSortIntern .>> smt2ws)

    do parseTermRefIntern :=
        let parseQualIdentifierWithTerm =
            betweenPara
                ((parseQualIdentifierIntern .>> smt2ws) .>>. many1 (parseTermIntern .>> smt2ws))
        let parseGenericBinding keyword bindingparser =
            betweenPara
                (str keyword >>. smt2ws >>. betweenPara (many1 (bindingparser .>> smt2ws) ) .>> smt2ws .>> smt2ws .>>. (parseTermIntern .>> smt2ws))
        let parseLetBinding    = parseGenericBinding "let"    parseVarBindingIntern
        let parseForallBinding = parseGenericBinding "forall" parseSortedVarIntern
        let parseExistsBinding = parseGenericBinding "exists" parseSortedVarIntern
        let parseAttributedTerm =
            betweenPara
                ((str "!" >>. smt2ws >>. parseTermIntern .>> smt2ws) .>>. many1 (parseAttributeIntern .>> smt2ws))

        choice [ attempt parseSpecConstantIntern     |>> Term.TermSpecConstant;
                 attempt parseQualIdentifierIntern   |>> Term.TermQualIdentifier;
                 attempt parseQualIdentifierWithTerm |>> Term.TermQualIdTerm;
                 attempt parseLetBinding             |>> Term.TermLetTerm;
                 attempt parseForallBinding          |>> Term.TermForAllTerm;
                 attempt parseExistsBinding          |>> Term.TermExistsTerm;
                 attempt parseAttributedTerm         |>> Term.TermExclimationPt;
               ]
    

    // Parse 3.9 Command Scripts Part 0 (Common part)
    let parseBValueIntern =
        choice [ str "true"  >>% true;
                 str "false" >>% false
               ]


    // Members of Type
    // Lexicons
    member this.parseNumeral        : Parser<_,unit> = parseNumeralIntern
    member this.parseDecimal        : Parser<_,unit> = parseDecimalIntern
    member this.parseHexadecimal    : Parser<_,unit> = parseHexadecimalIntern
    member this.parseBinary         : Parser<_,unit> = parseBinaryIntern
    member this.parseString         : Parser<_,unit> = parseStringIntern
    member this.parseReservedWord   : Parser<_,unit> = parseReservedWordIntern
    member this.parseSymbol         : Parser<_,unit> = parseSymbolIntern
    member this.parseKeyword        : Parser<_,unit> = parseKeywordIntern
    // S-expressions
    member this.parseDecoratedSExpr : Parser<_,unit> = parseDecoratedSExprIntern
    member this.parseSpecConstant   : Parser<_,unit> = parseSpecConstantIntern
    member this.parseSExpr          : Parser<_,unit> = parseSExprIntern
    // Identifiers
    member this.parseIdentifier     : Parser<_,unit> = parseIdentifierIntern
    // Attributes
    member this.parseAttributeValue : Parser<_,unit> = parseAttributeValueIntern
    member this.parseAttribute      : Parser<_,unit> = parseAttributeIntern
    // Sorts
    member this.parseSort           : Parser<_,unit> = parseSortIntern
    // Terms and Formulas
    member this.parseQualIdentifier : Parser<_,unit> = parseQualIdentifierIntern
    member this.parseVarBinding     : Parser<_,unit> = parseVarBindingIntern
    member this.parseSortedVar      : Parser<_,unit> = parseSortedVarIntern
    member this.parseTerm           : Parser<_,unit> = parseTermIntern
    // Command Scripts Part 0 (Common part)
    member this.parseBValue         : Parser<_,unit> = parseBValueIntern


    // custom function for the stream-reader


(*
    Tokenizer, der benutzt werden kann, um bspw. eine SExpression aus einem Stream zu isolieren, ohne zu wissen, ob der Stream bereits zu Ende ist. 
    (FParsec versucht immer erst das Ende eines Streams abzuwarten, versucht dann erst zu parsen. Dies ist für den interaktiven Modus aber nicht
     möglich)
        choice [ attempt parseSpecConstantIntern   |>> SExpr.SExprSpecConstant;
                 attempt parseSymbolIntern         |>> SExpr.SExprSymbol;
                 attempt parseKeywordIntern        |>> SExpr.SExprKeyword;
                         parseDecoratedSExprIntern |>> SExpr.SExprSExprList
               ]
        Wir registrieren einfach das erste Zeichen ungleich "(", Falls sowas einfaches, dann gehen wir nach rechts bis zum ersten leerzeichen oder dem zeilenende.
        Ansonsten Zählen wir "(" und ")" mit. Achtung: Wenn wir auf ein ";" Treffen, so zählt die Zeile bis zum Zeilenende nicht mehr. Ansonsten
        achten wir auf "\"". Beginn und Ende eines Strings werden beachtet. Sollte im String ein Gänsefüßchen vorkommen. So wird dies ignoriert. TODO: Quoted Strings überlegen
*)
exception SMTSExpressionTokenizerErrorException

type SMTSExpressionTokenizer () =
    let mutable MyInCommentary : bool = false
    let mutable MyInString : bool = false
    let mutable MyInStringAndEscapeChar : bool = false
    let mutable MyInQuotedSymbol : bool = false
    let mutable MyOpenParanthesis : int = 0
    let mutable MyComplete : bool = false
    let mutable MyStringUnproccessed = new System.Text.StringBuilder ()
    let mutable MyStringProccessed  = new System.Text.StringBuilder ()
    let mutable MyReadSymbolStringSpecOrKeyword : bool = false
    let mutable MyProccessingError : bool = false

    member this.ParseNewInput (str:string) : bool =
        let isWhitespace chr = 
            match chr with 
                | '\n' -> true
                | ' '  -> true
                | '\r' -> true
                | '\t' -> true
                | _ -> false                        
        MyStringUnproccessed.Append str |> ignore
        let mutable toRemove = 0
        for ctr in 0..(MyStringUnproccessed.Length-1) do        
            if MyComplete <> true then
                toRemove <- toRemove + 1
                let chr = MyStringUnproccessed.Chars ctr
                (MyStringProccessed.Append chr |>ignore )

                if MyInCommentary = true then
                    // commentary mode
                    match chr with
                        | '\n' -> MyInCommentary<-false
                        | _ -> ()
                elif MyInString = true then
                    // quoted string mode
                    if chr = '\\' && not MyInStringAndEscapeChar then
                        MyInStringAndEscapeChar <- true
                    elif chr = '"' && not MyInStringAndEscapeChar then
                        MyInString <- false
                        MyReadSymbolStringSpecOrKeyword <- true
                    elif MyInStringAndEscapeChar then
                        MyInStringAndEscapeChar <- false
                elif MyInQuotedSymbol = true then
                    if chr = '\\' then
                        raise SMTSExpressionTokenizerErrorException                    
                    elif chr = '|' then
                        MyInQuotedSymbol <- false
                        MyReadSymbolStringSpecOrKeyword <- true
                else
                    // normal mode
                    if chr = '(' then
                        MyOpenParanthesis <- MyOpenParanthesis + 1
                    elif chr = ')' then
                        MyOpenParanthesis <- MyOpenParanthesis - 1
                        if MyOpenParanthesis = 0 then MyComplete <- true
                    elif chr = '"' then
                        MyInString <- true
                    elif chr = ';' then
                        MyInCommentary <- true
                    elif chr = '|' then
                        MyInQuotedSymbol <- true
                    elif not (isWhitespace chr) then
                        MyReadSymbolStringSpecOrKeyword <- true                                       
            elif MyComplete = true then
                ()
        if MyReadSymbolStringSpecOrKeyword && MyOpenParanthesis = 0 && MyInQuotedSymbol = false && MyInString = false then
            MyComplete <- true
        MyStringUnproccessed.Remove(0,toRemove) |> ignore
        MyComplete
        
    member this.StringProccessed
        with get () : string = MyStringProccessed.ToString ()
        
    member this.StringUnproccessed
        with get () : string = MyStringUnproccessed.ToString ()
        