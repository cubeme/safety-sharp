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

namespace SafetySharp.Models
open SafetySharp.Models.Sam

module internal SamParser =

    // The statement and expression parser is similar to the FIL-parser, but the Data Structures are different.
    
    [<RequireQualifiedAccess>]
    type IdentifierType =
        | GlobalVar
        | LocalVar
    
    type UserState = {
        IdentifierToType : Map<string,IdentifierType>;
    }
        with
            static member initial =
                {
                    UserState.IdentifierToType = Map.empty<string,IdentifierType>;
                }
            member us.IsIdentifierOfType str (id_type:IdentifierType) =
                if us.IdentifierToType.ContainsKey str && (us.IdentifierToType.Item str) = id_type then
                    true
                else
                    false       
            member us.addIdentifier (identifier:string,_type:IdentifierType) =
                { us with
                    UserState.IdentifierToType = us.IdentifierToType.Add(identifier,_type)
                }

    open FParsec
    open SafetySharp.GenericParsers

    
    let parseIdentifier<'us> : Parser<string,'us> = identifier (IdentifierOptions())

    let parseIdentifierDecl (id_type:IdentifierType) : Parser<_,UserState> =
        fun stream ->
            let identifier = (parseIdentifier stream)
            if identifier.Status = ReplyStatus.Ok then
                stream.UserState <- stream.UserState.addIdentifier (identifier.Result, id_type)
                Reply(identifier.Status,identifier.Result,identifier.Error)
            else
                Reply(identifier.Status,identifier.Error)

    let parseIdentifierInst (id_type:IdentifierType) : Parser<_,UserState> =
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

    // parses the Boolean constants true or false, yielding a Boolean AST node
    let trueKeyword : Parser<_,UserState> =
        stringReturn "true" (Val.BoolVal true)
    let falseKeyword  : Parser<_,UserState> =
        stringReturn "false" (Val.BoolVal false)

    // parses the Boolean constants, but not, e.g., truee or false1, 
    let boolean : Parser<_,UserState> =
        let isIdentifierChar c = isLetter c || isDigit c || c = '_'
        (trueKeyword <|> falseKeyword) .>>? (notFollowedBy (many1Satisfy isIdentifierChar))

    // parses a number
    let number : Parser<_,UserState> =
        many1Satisfy isDigit |>> (fun value -> value |> bigint.Parse |> Val.NumbVal)
        
    let parseReal : Parser<_,UserState> =
        let decimalToVal (dec:string) =
            System.Convert.ToDouble(dec) |> Val.RealVal
        parseDecimal |>> decimalToVal
        
    let value : Parser<_,UserState> =
        boolean <|> parseReal<|> number        
        
    let probVal : Parser<_,UserState> =
        let decimalToVal (dec:string) =
            System.Convert.ToDouble(dec,System.Globalization.CultureInfo.InvariantCulture) |> Val.ProbVal
        parseDecimal |>> decimalToVal

    // parses an identifier of a variable 
    let localVarIdDecl : Parser<_,UserState> =
        parseIdentifierDecl IdentifierType.LocalVar |>> Var.Var

    let globalVarIdDecl : Parser<_,UserState> =
        parseIdentifierDecl IdentifierType.GlobalVar |>> Var.Var
                
    let localVarIdInst : Parser<_,UserState> =
        parseIdentifierInst IdentifierType.LocalVar |>> Var.Var

    let globalVarIdInst : Parser<_,UserState> =
        parseIdentifierInst IdentifierType.GlobalVar |>> Var.Var
                
    let elementIdInst: Parser<_,UserState> =
        (attempt globalVarIdInst |>> Element.GlobalVar) <|>
        (localVarIdInst |>> Element.LocalVar)

    // parsers with space afterwards
    let pstring_ws s = pstring s .>> spaces
    let boolean_ws = boolean .>> spaces
    let number_ws = number .>> spaces
    let value_ws = value .>> spaces
    let probVal_ws = probVal .>> spaces
    let localVarIdDecl_ws = localVarIdDecl .>> spaces
    let globalVarIdDecl_ws = globalVarIdDecl .>> spaces
    let elementIdInst_ws = elementIdInst .>> spaces
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
        opp.AddOperator(InfixOperator("!="  , spaces , 3, Associativity.Left, fun e1 e2 -> BExpr(e1, BOp.NotEquals, e2)))
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
            (pstring_ws "prev") >>. parentOpen_ws >>. elementIdInst_ws .>> parentClose_ws

        // recursive term parser for expressions
        opp.TermParser <- (boolean_ws |>> Expr.Literal) <|> (prevExpr_ws |>> Expr.Read) <|> (number_ws |>> Expr.Literal) <|> (elementIdInst_ws |>> Expr.Read) <|> parenExpr_ws
        opp.ExpressionParser
        
    let (guardedCommandClause:Parser<_,UserState>),guardedCommandClauseRef = createParserForwardedToRef()
    let (statement:Parser<_,UserState>),statementRef = createParserForwardedToRef()
    
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
            attempt (tuple2 (elementIdInst_ws .>> (pstring_ws ":="))
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

    let globalVarDecl_ws : Parser<_,UserState> =
        let createVarDecl var _type inits =
            {
                GlobalVarDecl.Var = var ;
                GlobalVarDecl.Type = _type ;
                GlobalVarDecl.Init = inits;
            }
        pipe3 (globalVarIdDecl_ws .>> (pstring_ws ":"))
              (typeExtended_ws .>> (pstring_ws "="))
              ((sepBy1 value_ws (pstring_ws ",")) .>> (pstring_ws ";"))
              createVarDecl
              
    let globalVarDecls_ws =
        (many globalVarDecl_ws)
        
    let localVarDecl_ws : Parser<_,UserState> =
        let createVarDecl var _type =
            {
                LocalVarDecl.Var = var ;
                LocalVarDecl.Type = _type ;
            }
        pipe2 (localVarIdDecl_ws .>> (pstring_ws ":"))
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
        spaces >>. pgm_ws .>> eof


    let parseSamFile_Result (str:string) : Pgm =
        let parser = samFile 
        let parsedString = runParserOnString parser (UserState.initial) "" str
        match parsedString with
            | Success(result, _, _)   -> result
            | Failure(errorMsg, a, b) -> failwith errorMsg

        
    open SafetySharp.Workflow
    open SafetySharp.Models.ScmTracer

    let parseStringWorkflow : ExogenousWorkflowFunction<string,SamTracer.SamTracer<Sam.Traceable>> = workflow {
        let! model = SafetySharp.Workflow.getState ()
        do! SamTracer.setInitialSamModel (parseSamFile_Result model)
        return ()
    }