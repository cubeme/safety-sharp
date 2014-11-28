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

namespace SafetySharp.Internal.ModelFile.Parser


module internal ParseModelFile =

    open FParsec
    open Test
    
    [<RequireQualifiedAccess>]
    type IdentifierType =
        | Field
        | Var
        | NotDeclared

    type UserState = {
        TypeOfIdentifier : Map<string,IdentifierType> ;
    }
        with
            member us.IsIdentifierOfType str (id_type:IdentifierType) =
                if us.TypeOfIdentifier.ContainsKey str then
                    if (us.TypeOfIdentifier.Item str) = id_type then
                        true
                    else
                        false
                else
                    false
            static member initialUserState =
                {
                    UserState.TypeOfIdentifier = Map.empty<string,IdentifierType>;
                }
    
    type GuardedCommandClause = Expr * Stm
    

    // parses the Boolean constants true or false, yielding a Boolean AST node
    let trueKeyword : Parser<_,UserState> =
        stringReturn "true" (Val.BoolVal true |> Expr.Literal)
    let falseKeyword  : Parser<_,UserState> =
        stringReturn "false" (Val.BoolVal false |> Expr.Literal)

    // parses the Boolean constants, but not, e.g., truee or false1, 
    let boolVal : Parser<_,UserState> =
        let isIdentifierChar c = isLetter c || isDigit c || c = '_'
        (trueKeyword <|> falseKeyword) .>>? (notFollowedBy (many1Satisfy isIdentifierChar))

    // parses a number
    let number : Parser<_,UserState> =
        many1Satisfy isDigit |>> ( fun value -> (bigint.Parse value |> int32 |> Val.IntVal |> Expr.Literal ))
        
    let parseIdentifierDecl (id_type:IdentifierType) : Parser<_,UserState> =        
        let parseIdentifier = identifier (IdentifierOptions())
        fun stream ->
            let identifier = (parseIdentifier stream)
            if identifier.Status = ReplyStatus.Ok then
                stream.UserState <- { stream.UserState with UserState.TypeOfIdentifier = stream.UserState.TypeOfIdentifier.Add(identifier.Result, id_type)}
                Reply(identifier.Status,identifier.Result,identifier.Error)
            else
                Reply(identifier.Status,identifier.Error)

    let parseIdentifierInst (id_type:IdentifierType) : Parser<_,UserState> =        
        let parseIdentifier = identifier (IdentifierOptions())
        fun stream ->
            let identifier = (parseIdentifier stream)
            if identifier.Status = ReplyStatus.Ok then
                if stream.UserState.IsIdentifierOfType identifier.Result id_type then
                    Reply(identifier.Status,identifier.Result,identifier.Error)
                else
                    let error = messageError (sprintf "Identifier '%s' has not been declared or the kind of access is wrong" identifier.Result)
                    Reply(ReplyStatus.Error,mergeErrors identifier.Error error)
            else
                Reply(identifier.Status,identifier.Error)


    // parse identifier of variables, fields, ports and components
    let varIdDecl: Parser<_,UserState> =
        parseIdentifierDecl IdentifierType.Var |>> Var.Var
    let varIdInst: Parser<_,UserState> =
        parseIdentifierInst IdentifierType.Var |>> Var.Var
    

    let fieldIdDecl: Parser<_,UserState> =
        parseIdentifierDecl IdentifierType.Field |>> Field.Field
    let fieldIdInst: Parser<_,UserState> =
        parseIdentifierInst IdentifierType.Field |>> Field.Field

                
    let reqPortId: Parser<_,UserState> =
        ((identifier (IdentifierOptions())) |>> ReqPort.ReqPort)                
    let provPortId: Parser<_,UserState> =
        ((identifier (IdentifierOptions())) |>> ProvPort.ProvPort)
    let compId : Parser<_,UserState> =
        ((identifier (IdentifierOptions())) |>> Comp.Comp)

(*
    // parsers with space afterwards
    let pstring_ws s = pstring s .>> spaces
    let boolVal_ws = boolVal .>> spaces
    let number_ws = number .>> spaces
    let varId_ws = varId .>> spaces
    let fieldId_ws = fieldId .>> spaces
    let reqPortId_ws = reqPortId .>> spaces
    let provPortId_ws = provPortId .>> spaces
    let compId_ws = compId .>> spaces
    let parentOpen_ws = pstring_ws "("
    let parentClose_ws = pstring_ws ")"

    // parses an expression
    let expression : Parser<_,UserState> =
        let opp = new OperatorPrecedenceParser<_,_,_>()        
        opp.AddOperator(InfixOperator("/"   , spaces , 5, Associativity.Left, fun e1 e2 -> BExpr(e1, BOp.Divide, e2)))
        opp.AddOperator(InfixOperator("*"   , spaces , 5, Associativity.Left, fun e1 e2 -> BExpr(e1, BOp.Multiply, e2)))
        opp.AddOperator(InfixOperator("%"   , spaces , 5, Associativity.Left, fun e1 e2 -> BExpr(e1, BOp.Modulo, e2)))
        // >
        opp.AddOperator(InfixOperator("+"   , spaces , 4, Associativity.Left, fun e1 e2 -> BExpr(e1, BOp.Add, e2)))
        opp.AddOperator(InfixOperator("-"   , spaces .>> notFollowedByString ">>" , 4, Associativity.Left, fun e1 e2 -> BExpr(e1, BOp.Subtract, e2)))
        // >
        opp.AddOperator(InfixOperator("<="  , spaces , 3, Associativity.Left, fun e1 e2 -> BExpr(e1, BOp.LessEqual, e2)))
        opp.AddOperator(InfixOperator("=="  , spaces , 3, Associativity.Left, fun e1 e2 -> BExpr(e1, BOp.Equals, e2)))
        opp.AddOperator(InfixOperator("=/=" , spaces , 3, Associativity.Left, fun e1 e2 -> BExpr(e1, BOp.NotEquals, e2)))
        opp.AddOperator(InfixOperator(">="  , spaces , 3, Associativity.Left, fun e1 e2 -> BExpr(e1, BOp.GreaterEqual, e2)))
        opp.AddOperator(InfixOperator(">"   , spaces , 3, Associativity.Left, fun e1 e2 -> BExpr(e1, BOp.Greater, e2)))
        opp.AddOperator(InfixOperator("<"   , spaces , 3, Associativity.Left, fun e1 e2 -> BExpr(e1, BOp.Less, e2)))
        opp.AddOperator(PrefixOperator("!", spaces, 3, true, fun e -> UExpr(e,UOp.Not)))
        //>
        opp.AddOperator(InfixOperator("&&"   , spaces , 2, Associativity.Left, fun e1 e2 -> BExpr(e1, BOp.And, e2)))
        //>
        opp.AddOperator(InfixOperator("||"   , spaces , 1, Associativity.Left, fun e1 e2 -> BExpr(e1, BOp.Or, e2)))

        // parses an expression between ( and )
        let parenExpr_ws = between parentOpen_ws parentClose_ws (opp.ExpressionParser)
        
        let parseFieldParameterOrLocal =
            

        // recursive term parser for expressions
        opp.TermParser <- boolVal_ws <|> number_ws <|> (variable_ws |>> Expression.ReadVariable) <|> parenExpr_ws
        opp.ExpressionParser
        
    let guardedCommandClause,guardedCommandClauseRef = createParserForwardedToRef()
    let statement,statementRef = createParserForwardedToRef()
    
    let expression_ws = expression .>> spaces
    let guardedCommandClause_ws = guardedCommandClause .>> spaces
    let statement_ws = statement .>> spaces


    do guardedCommandClauseRef :=
       (expression_ws .>>. ((pstring_ws "->>") >>. (pstring_ws "{") >>. statement_ws .>> (pstring_ws "}"))) |>> (fun (guard,stmnt) -> (guard,stmnt) )
        
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
            if stmnts.Length = 1 then
                    stmnts.Head
                else
                    Statement.BlockStatement stmnts
        sepBy1 (allExceptSeq_ws) (pstring_ws ";") |>> refurbishResult

        *)