﻿// The MIT License (MIT)
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

namespace SafetySharp.Models
open SafetySharp.Models.Sam

module internal SamParser =

    // The statement and expression parser is similar to the FIL-parser, but the Data Structures are different.

    open FParsec
    open SafetySharp.GenericParsers

    // parses the Boolean constants true or false, yielding a Boolean AST node
    let trueKeyword : Parser<_,unit> =
        stringReturn "true" (Val.BoolVal true)
    let falseKeyword  : Parser<_,unit> =
        stringReturn "false" (Val.BoolVal false)

    // parses the Boolean constants, but not, e.g., truee or false1, 
    let boolean : Parser<_,unit> =
        let isIdentifierChar c = isLetter c || isDigit c || c = '_'
        (trueKeyword <|> falseKeyword) .>>? (notFollowedBy (many1Satisfy isIdentifierChar))

    // parses a number
    let number : Parser<_,unit> =
        many1Satisfy isDigit |>> (fun value -> value |> bigint.Parse |> Val.NumbVal)
        
    let parseReal : Parser<_,unit> =
        let decimalToVal (dec:string) =
            System.Convert.ToDouble(dec) |> Val.RealVal
        parseDecimal |>> decimalToVal
        
    let value : Parser<_,unit> =
        boolean <|> parseReal<|> number        
        
    let probVal : Parser<_,unit> =
        let decimalToVal (dec:string) =
            System.Convert.ToDouble(dec) |> Val.ProbVal
        parseDecimal |>> decimalToVal

    // parses an identifier of a variable 
    let variable : Parser<_,unit> =
        ((identifier (IdentifierOptions())) |>> Var)

    // parsers with space afterwards
    let pstring_ws s = pstring s .>> spaces
    let boolean_ws = boolean .>> spaces
    let number_ws = number .>> spaces
    let value_ws = value .>> spaces
    let probVal_ws = probVal .>> spaces
    let variable_ws = variable .>> spaces
    let parentOpen_ws = pstring_ws "("
    let parentClose_ws = pstring_ws ")"

    // parses an expression
    let expression : Parser<_,unit> =
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

        // parses a read operation of the previous value of a variable
        let prevExpr_ws =
            (pstring_ws "prev") >>. parentOpen_ws >>. variable_ws .>> parentClose_ws

        // recursive term parser for expressions
        opp.TermParser <- (boolean_ws |>> Expr.Literal) <|> (prevExpr_ws |>> Expr.Read) <|> (number_ws |>> Expr.Literal) <|> (variable_ws |>> Expr.Read) <|> parenExpr_ws
        opp.ExpressionParser
        
    let (guardedCommandClause:Parser<_,unit>),guardedCommandClauseRef = createParserForwardedToRef()
    let (statement:Parser<_,unit>),statementRef = createParserForwardedToRef()
    
    let expression_ws = expression .>> spaces
    let guardedCommandClause_ws = guardedCommandClause .>> spaces
    let statement_ws = statement .>> spaces
    
    
    let probability_expression =
        let opp = new OperatorPrecedenceParser<_,_,_>()        
        opp.AddOperator(InfixOperator("/"   , spaces , 5, Associativity.Left, fun e1 e2 -> Expr.BExpr(e1, BOp.Divide, e2)))
        opp.AddOperator(InfixOperator("*"   , spaces , 5, Associativity.Left, fun e1 e2 -> Expr.BExpr(e1, BOp.Multiply, e2)))
        // >
        opp.AddOperator(InfixOperator("+"   , spaces , 4, Associativity.Left, fun e1 e2 -> Expr.BExpr(e1, BOp.Add, e2)))
        opp.AddOperator(InfixOperator("-"   , spaces .>> notFollowedByString ">" , 4, Associativity.Left, fun e1 e2 -> Expr.BExpr(e1, BOp.Subtract, e2)))
        // parses an expression between ( and )
        let parenExpr_ws = between parentOpen_ws parentClose_ws (opp.ExpressionParser)
        // recursive term parser for expressions
        opp.TermParser <-
            (probVal_ws |>> Expr.Literal) <|> (parenExpr_ws)
        opp.ExpressionParser
    let probability_expression_ws = probability_expression .>> spaces
    let stochasticClause,stochasticClauseRef = createParserForwardedToRef()
    let stochasticClause_ws = stochasticClause .>> spaces
    do stochasticClauseRef :=
       tuple2 (probability_expression .>> (pstring_ws "=>") .>> (pstring_ws "{") )
              ((many statement_ws |>> Stm.Block) .>> (pstring_ws "}"))
    
    do guardedCommandClauseRef :=
       pipe2 (expression_ws .>> (pstring_ws "=>") .>> (pstring_ws "{") )
             ((many statement_ws |>> Stm.Block) .>> (pstring_ws "}"))
             (fun guard stm -> {Clause.Guard=guard;Clause.Statement=stm})
        
    do statementRef :=
        let parseBlock =
            attempt (pstring_ws "{") >>. many statement_ws .>> (pstring_ws "}") |>> Stm.Block
        let parseChoice =
            attempt (pstring_ws "choice") >>. (pstring_ws "{") >>.
                    ((many guardedCommandClause_ws) |>> Stm.Choice ) .>>
                    (pstring_ws "}")  
        let parseStochastic =
            attempt (pstring_ws "stochastic") >>. (pstring_ws "{") >>.
                    ((many stochasticClause_ws) |>> Stm.Stochastic ) .>>
                    (pstring_ws "}")      
        let parseAssignment =
            attempt (tuple2 (variable_ws .>> (pstring_ws ":="))
                            (expression_ws .>> (pstring_ws ";")) |>> Stm.Write)     
        let allKindsOfStatements =
            parseAssignment <|>
            parseBlock <|>
            parseChoice <|>
            parseStochastic
        allKindsOfStatements

        
    let typeBasic_ws =
        let boolType = stringReturn "bool" Type.BoolType
        let intType = stringReturn "int" Type.IntType
        let realType = stringReturn "real" Type.RealType
        (boolType <|> intType <|> realType) .>> spaces
        
    let overflowBehavior_ws =
        let error = stringReturn "error on overrun" OverflowBehavior.Error
        let clamp = stringReturn "clamp on overrun" OverflowBehavior.Clamp
        let wraparound = stringReturn "wrap around on overrun" OverflowBehavior.WrapAround
        (error <|> clamp <|> wraparound) .>> spaces
    
    let typeExtended_ws =
        let rangedIntType =
            let createRangedIntType _from _to _overflow =
                match _overflow with
                    | Some(_overflow) -> Type.RangedIntType(int32 _from,int32 _to,_overflow)
                    | None -> Type.RangedIntType(int32 _from,int32 _to,OverflowBehavior.Error)
            pipe3 ((pstring_ws "int<") >>. parseBigint_ws .>> (pstring_ws ".."))
                  (parseBigint_ws)
                  ((opt ((pstring_ws",")>>. overflowBehavior_ws)) .>> pstring_ws ">")
                  createRangedIntType
        let rangedRealType =
            let createRangedRealType (_from:string) (_to:string) _overflow =
                match _overflow with
                    | Some(_overflow) -> Type.RangedRealType(System.Convert.ToDouble(_from),System.Convert.ToDouble(_to),_overflow)
                    | None -> Type.RangedRealType(System.Convert.ToDouble(_from),System.Convert.ToDouble(_to),OverflowBehavior.Error)
            pipe3 ((pstring_ws "real<") >>. parseDecimal_ws .>> (pstring_ws ".."))
                  (parseDecimal_ws)
                  ((opt ((pstring_ws",")>>. overflowBehavior_ws)) .>> pstring_ws ">")
                  createRangedRealType
        (rangedIntType <|> rangedRealType <|> typeBasic_ws)

    let globalVarDecl_ws : Parser<_,unit> =
        let createVarDecl var _type inits =
            {
                GlobalVarDecl.Var = var ;
                GlobalVarDecl.Type = _type ;
                GlobalVarDecl.Init = inits;
            }
        pipe3 (variable_ws .>> (pstring_ws ":"))
              (typeExtended_ws .>> (pstring_ws "="))
              ((sepBy1 value_ws (pstring_ws ",")) .>> (pstring_ws ";"))
              createVarDecl
              
    let globalVarDecls_ws =
        (many globalVarDecl_ws)
        
    let localVarDecl_ws : Parser<_,unit> =
        let createVarDecl var _type =
            {
                LocalVarDecl.Var = var ;
                LocalVarDecl.Type = _type ;
            }
        pipe2 (variable_ws .>> (pstring_ws ":"))
              (typeBasic_ws .>> (pstring_ws ";"))
              createVarDecl

    let localVarDecls_ws =
        (many localVarDecl_ws)

    let pgm_ws =
        let createPgm globals locals body =
            {
                Pgm.Globals = globals;
                Pgm.Locals = locals;
                Pgm.Body = body;
            }
        pipe3 (pstring_ws "globals" >>. pstring_ws "{" >>.  globalVarDecls_ws .>> pstring_ws "}")
              (pstring_ws "locals" >>. pstring_ws "{" >>.  localVarDecls_ws .>> pstring_ws "}")
              (many statement_ws |>> Stm.Block )
              createPgm              
    
    let samFile =
        spaces >>. pgm_ws



        
    open SafetySharp.Workflow
    open SafetySharp.Models.ScmWorkflow

    let parseStringWorkflow : LoadWorkflowFunction<string,Pgm,Traceable,unit> = workflow {
        let parseWithParser parser str =
            match run parser str with
            | Success(result, _, _)   -> result
            | Failure(errorMsg, _, _) -> failwith errorMsg

            
        let! model = SafetySharp.Workflow.getState ()
        let parsedModel = parseWithParser (samFile .>> eof) model
        do! SafetySharp.Workflow.updateState parsedModel
        let traceables = parsedModel.getTraceables
        do! SafetySharp.Workflow.initializeTracer traceables
        return ()
    }