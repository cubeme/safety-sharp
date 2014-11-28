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

namespace SafetySharp.Internal.FIL.Parser


module internal ParseFIL =

    // The statement and expression parser is similar to the FIL-parser, but the Data Structures are different.

    open FParsec
    open SafetySharp.Internal.FIL

    // parses the Boolean constants true or false, yielding a Boolean AST node
    let trueKeyword : Parser<_,unit> =
        stringReturn "true" (Expression.BooleanLiteral true)
    let falseKeyword  : Parser<_,unit> =
        stringReturn "false" (Expression.BooleanLiteral false)

    // parses the Boolean constants, but not, e.g., truee or false1, 
    let boolean : Parser<_,unit> =
        let isIdentifierChar c = isLetter c || isDigit c || c = '_'
        (trueKeyword <|> falseKeyword) .>>? (notFollowedBy (many1Satisfy isIdentifierChar))

    // parses a number
    let number : Parser<_,unit> =
        many1Satisfy isDigit |>> bigint.Parse


    // parses an identifier of a variable 
    let variable : Parser<_,unit> =
        ((identifier (IdentifierOptions())) |>> Identifier.Identifier)

    // parsers with space afterwards
    let pstring_ws s = pstring s .>> spaces
    let boolean_ws = boolean .>> spaces
    let number_ws = number .>> spaces
    let variable_ws = variable .>> spaces
    let parentOpen_ws = pstring_ws "("
    let parentClose_ws = pstring_ws ")"

    // parses an expression
    let expression : Parser<_,unit> =
        let opp = new OperatorPrecedenceParser<_,_,_>()        
        opp.AddOperator(InfixOperator("/"   , spaces , 5, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Divide, e2)))
        opp.AddOperator(InfixOperator("*"   , spaces , 5, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Multiply, e2)))
        opp.AddOperator(InfixOperator("%"   , spaces , 5, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Modulo, e2)))
        // >
        opp.AddOperator(InfixOperator("+"   , spaces , 4, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Add, e2)))
        opp.AddOperator(InfixOperator("-"   , spaces .>> notFollowedByString ">>" , 4, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Subtract, e2)))        
        // >
        opp.AddOperator(InfixOperator("<="  , spaces , 3, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.LessThanOrEqual, e2)))
        opp.AddOperator(InfixOperator("=="  , spaces , 3, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Equals, e2)))
        opp.AddOperator(InfixOperator("=/=" , spaces , 3, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.NotEquals, e2)))
        opp.AddOperator(InfixOperator(">="  , spaces , 3, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.GreaterThanOrEqual, e2)))
        opp.AddOperator(InfixOperator(">"   , spaces , 3, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.GreaterThan, e2)))
        opp.AddOperator(InfixOperator("<"   , spaces , 3, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.LessThan, e2)))
        opp.AddOperator(PrefixOperator("!", spaces, 3, true, fun e -> UnaryExpression(e,UnaryOperator.LogicalNot)))
        //>
        opp.AddOperator(InfixOperator("&&"   , spaces , 2, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.LogicalAnd, e2)))
        //>
        opp.AddOperator(InfixOperator("||"   , spaces , 1, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.LogicalOr, e2)))

        // parses an expression between ( and )
        let parenExpr_ws = between parentOpen_ws parentClose_ws (opp.ExpressionParser)

        // parses a read operation of the previous value of a variable
        let prevExpr_ws =
            (pstring_ws "prev") >>. parentOpen_ws >>. variable_ws .>> parentClose_ws

        // recursive term parser for expressions
        opp.TermParser <- boolean_ws <|> (prevExpr_ws |>> Expression.ReadVariablePrev) <|> (number_ws |>> Expression.NumberLiteral) <|> (variable_ws |>> Expression.ReadVariable) <|> parenExpr_ws
        opp.ExpressionParser
        
    let (guardedCommandClause:Parser<_,unit>),guardedCommandClauseRef = createParserForwardedToRef()
    let (statement:Parser<_,unit>),statementRef = createParserForwardedToRef()
    
    let expression_ws = expression .>> spaces
    let guardedCommandClause_ws = guardedCommandClause .>> spaces
    let statement_ws = statement .>> spaces


    do guardedCommandClauseRef :=
       (expression_ws .>>. ((pstring_ws "->>") >>. (pstring_ws "{") >>. statement_ws .>> (pstring_ws "}"))) |>> GuardedCommandClause
        
    do statementRef :=
        let parseSkip =
            stringReturn "skip" Statement.EmptyStatement        //pstring_ws "skip" >>% Statement.EmptyStatement
        let parseGuardedCommand =
            attempt (sepBy (guardedCommandClause_ws) (pstring_ws "|||")) |>> Statement.GuardedCommandStatement
        let parseAssignment =
            attempt (variable_ws .>>. (pstring_ws ":=" >>. expression)) |>> Statement.WriteVariable            
        
        // a; b; c == (a ; b) ; c  //left associative (in semantics)
        let allExceptSeq = parseSkip <|> parseGuardedCommand <|> parseAssignment
        let allExceptSeq_ws = allExceptSeq .>> spaces
        
        let refurbishResult (stmnts : Statement list ) =
            (*let rec convertToSeqStmnt (stmnts : Statement list) (leftNode : Statement) =
                if stmnts.IsEmpty then
                    leftNode
                else
                    let newLeft = Statement.SeqStatement(leftNode,stmnts.Head)
                    convertToSeqStmnt (stmnts.Tail) (newLeft)
            convertToSeqStmnt (stmnts.Tail) (stmnts.Head)
            *)
            if stmnts.Length = 1 then
                    stmnts.Head
                else
                    Statement.BlockStatement stmnts

        sepBy1 (allExceptSeq_ws) (pstring_ws ";") |>> refurbishResult

    let filFile = spaces >>. statement_ws