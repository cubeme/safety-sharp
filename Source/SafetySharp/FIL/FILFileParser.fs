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

    open FParsec
    open SafetySharp.Internal.FIL

    // parses the Boolean constants true or false, yielding a Boolean AST node
    let trueKeyword : Parser<_,unit> =
        stringReturn "true" (Expression.BooleanLiteral true)
    let falseKeyword  : Parser<_,unit> =
        stringReturn "false" (Expression.BooleanLiteral true)

    // parses the Boolean constants //TODO:, but not, e.g., truee or false1, 
    let boolean : Parser<_,unit> =
        (trueKeyword <|> falseKeyword) 
                    //TODO .>>? (notFollowedBy (many1Satisfy isIdentifierChar))

    // parses a number
    let number : Parser<_,unit> =
        many1Satisfy isDigit |>> bigint.Parse


    // parses an identifier of a variable 
    let variable : Parser<_,unit> =
        ((identifier (IdentifierOptions())) |>> Identifier.Identifier)

    // parsers with space afterwards
    let boolean_ws = boolean .>> spaces
    let number_ws = number .>> spaces
    let variable_ws = variable .>> spaces
    let parentOpen_ws = pstring "(" .>> spaces
    let parentClose_ws = pstring ")" .>> spaces

    // parses an expression
    let expression : Parser<_,unit> =
        let opp = new OperatorPrecedenceParser<_,_,_>()        
        opp.AddOperator(InfixOperator("/"   , spaces , 5, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Divide, e2)))
        opp.AddOperator(InfixOperator("*"   , spaces , 5, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Divide, e2)))
        opp.AddOperator(InfixOperator("%"   , spaces , 5, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Divide, e2)))
        // >
        opp.AddOperator(InfixOperator("+"   , spaces , 4, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Divide, e2)))
        opp.AddOperator(InfixOperator("-"   , spaces , 4, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Divide, e2)))        
        // >
        opp.AddOperator(InfixOperator("<="  , spaces , 3, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Divide, e2)))
        opp.AddOperator(InfixOperator("=="  , spaces , 3, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Divide, e2)))
        opp.AddOperator(InfixOperator("=/=" , spaces , 3, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Divide, e2)))
        opp.AddOperator(InfixOperator(">="  , spaces , 3, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Divide, e2)))
        opp.AddOperator(InfixOperator(">"   , spaces , 3, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Divide, e2)))
        opp.AddOperator(InfixOperator("<"   , spaces , 3, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Divide, e2)))
        opp.AddOperator(PrefixOperator("!", spaces, 3, true, fun e -> UnaryExpression(e,UnaryOperator.LogicalNot)))
        //>
        opp.AddOperator(InfixOperator("&&"   , spaces , 2, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Divide, e2)))
        //>
        opp.AddOperator(InfixOperator("||"   , spaces , 1, Associativity.Left, fun e1 e2 -> BinaryExpression(e1, BinaryOperator.Divide, e2)))

        // parses an expression between ( and )
        let parenExpr_ws = between parentOpen_ws parentClose_ws (opp.ExpressionParser)

        // parses a read operation of the previous value of a variable
        let prevExpr_ws =
            (pstring "prev") >>. spaces >>. parentOpen_ws >>. variable_ws .>> parentClose_ws

        // recursive term parser for expressions
        opp.TermParser <- boolean <|> (prevExpr_ws |>> Expression.ReadVariablePrev) <|> (number_ws |>> Expression.NumberLiteral) <|> (variable_ws |>> Expression.ReadVariable) <|> parenExpr_ws
        opp.ExpressionParser



        