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


    // TODO: Remove, when context changes (i.e. switch to push, pop)
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
    
    let pipe7 p1 p2 p3 p4 p5 p6 p7 f =
        pipe4 p1 p2 p3 (tuple4 p4 p5 p6 p7)
            (fun x1 x2 x3 (x4, x5, x6, x7) -> f x1 x2 x3 x4 x5 x6 x7)


    // parses the Boolean constants true or false, yielding a Boolean AST node
    let trueKeyword : Parser<_,UserState> =
        stringReturn "true" (Val.BoolVal true)
    let falseKeyword  : Parser<_,UserState> =
        stringReturn "false" (Val.BoolVal false)

    // parses the Boolean constants, but not, e.g., truee or false1, 
    let boolVal : Parser<_,UserState> =
        let isIdentifierChar c = isLetter c || isDigit c || c = '_'
        (trueKeyword <|> falseKeyword) .>>? (notFollowedBy (many1Satisfy isIdentifierChar))

    // parses a number
    let numberVal : Parser<_,UserState> =
        many1Satisfy isDigit |>> ( fun value -> (bigint.Parse value |> int32 |> Val.IntVal ))

    let value : Parser<_,UserState> =
        boolVal <|> numberVal        
        
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
                
    let pushUserStateStackComponent : Parser<_,UserState> =
        spaces // TODO
     
    let popUserStateStackComponent : Parser<_,UserState> =
        spaces // TODO

    let pushUserStateStackCall : Parser<_,UserState> =
        spaces // TODO
     
    let popUserStateStackCall : Parser<_,UserState> =
        spaces // TODO

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

    // parsers with space afterwards
    let pstring_ws s : Parser<_,UserState> =
        pstring s .>> spaces
    let boolVal_ws = boolVal .>> spaces
    let numberVal_ws = numberVal .>> spaces
    let value_ws = value .>> spaces
    let varIdDecl_ws = varIdDecl .>> spaces
    let varIdInst_ws = varIdInst .>> spaces
    let fieldIdDecl_ws = fieldIdDecl .>> spaces
    let fieldIdInst_ws = fieldIdInst .>> spaces
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
        
        //let parseFieldParameterOrLocal =
            

        // recursive term parser for expressions
        opp.TermParser <-
            (boolVal_ws |>> Expr.Literal) <|> 
            (numberVal_ws |>> Expr.Literal) <|>
            (fieldIdInst_ws |>> Expr.ReadField) <|>
            (varIdInst_ws |>> Expr.ReadVar) <|> 
            (parenExpr_ws)

        opp.ExpressionParser
        
    let (guardedCommandClause:Parser<_,UserState>),guardedCommandClauseRef = createParserForwardedToRef()
    let (statement:Parser<_,UserState>),statementRef = createParserForwardedToRef()
    
    let expression_ws = expression .>> spaces
    let guardedCommandClause_ws = guardedCommandClause .>> spaces
    let statement_ws = statement .>> spaces

    let expressions_ws = sepBy expression_ws (pstring_ws ",")
    let varIdInsts_ws = sepBy varIdInst_ws (pstring_ws ",")

    do guardedCommandClauseRef :=
       (expression_ws .>>. ((pstring_ws "->>") >>. (pstring_ws "{") >>. statement_ws .>> (pstring_ws "}"))) |>> (fun (guard,stmnt) -> (guard,stmnt) )
        
    do statementRef :=
        let parseSkip =
            stringReturn "skip" Stm.Skip
        let parseGuardedCommand =
            attempt (sepBy (guardedCommandClause_ws) (pstring_ws "|||")) |>> Stm.GrdCmd
        let parseFieldAssignment =
            attempt (fieldIdInst_ws .>>. (pstring_ws ":=" >>. expression)) |>> Stm.AssignField
        let parseVariableAssignment =
            attempt (varIdInst_ws .>>. (pstring_ws ":=" >>. expression)) |>> Stm.AssignVar
        let parsePortCall =
            attempt (tuple3 (reqPortId_ws .>> parentOpen_ws) (expressions_ws .>> (pstring_ws ";")) (varIdInsts_ws .>> parentClose_ws)) |>> Stm.CallPort
        let parseBehCall =
            attempt (compId_ws.>> parentOpen_ws .>> parentClose_ws) |>> Stm.CallComp


        // a; b; c == (a ; b) ; c  //left associative (in semantics)
        let allExceptSeq =
            parseSkip <|>
            parseGuardedCommand <|>
            parseFieldAssignment <|>
            parseVariableAssignment <|>
            parsePortCall <|>
            parseBehCall

        let allExceptSeq_ws = allExceptSeq .>> spaces
        
        let refurbishResult (stmnts : Stm list ) =
            if stmnts.Length = 1 then
                    stmnts.Head
                else
                    Stm.Block stmnts
        sepBy1 (allExceptSeq_ws) (pstring_ws ";") |>> refurbishResult

    let type_ws =
        let boolType = stringReturn "bool" Type.BoolType
        let intType = stringReturn "int"  Type.IntType
        (boolType <|> intType) .>> spaces
    
    let typedVarDecl_ws : Parser<_,UserState> =
        let createVarSym var _type =
            {
                VarSym.Var = var ;
                VarSym.Type = _type ;
            }
        pipe2 (varIdDecl_ws .>> (pstring_ws ":" )) 
              (type_ws)
              createVarSym

    let typedVarDeclSection_ws =
        sepBy typedVarDecl_ws (pstring_ws ",")
    
    let behaviour =
        tuple2 ((pstring_ws "behaviour")>>. (pstring_ws "{")  >>. typedVarDeclSection_ws .>> (pstring_ws "."))
               ((statement_ws) .>> (pstring "}"))

    let behaviour_ws = behaviour .>> spaces
    
    let (comp:Parser<_,UserState>), compRef = createParserForwardedToRef()
    let comp_ws = comp .>> spaces

    let typedFieldDecl_ws : Parser<_,UserState> =        
        let createFieldSym var (init:Val list) =
            let _type = 
                match init.Head with
                    | Val.BoolVal(_) -> Type.BoolType
                    | Val.IntVal(_) -> Type.IntType
            {
                FieldSym.Field = var ;
                FieldSym.Type = _type ;
                FieldSym.Init = init ;
            }
        attempt (pipe2 (fieldIdDecl_ws .>> (pstring_ws "="))
                       (many1 value_ws)
                       createFieldSym)

    do compRef :=
        let createComponent comp subcomp fields reqPorts provPorts bindings (locals,stm) =
            {
                CompSym.Comp = comp;
                CompSym.Subcomp = subcomp;
                CompSym.Fields = fields;
                CompSym.ReqPorts = []; // TODO:  reqPorts;
                CompSym.ProvPorts = []; // TODO:  provPorts;
                CompSym.Bindings = []; // TODO:  bindings;
                CompSym.Locals = locals;
                CompSym.Stm = stm;
            }
        pipe7 ((pstring "component") >>. spaces1 >>. compId_ws .>> (pstring_ws "{"))
              (many comp_ws)
              (many typedFieldDecl_ws)
              (spaces)
              (spaces)
              (spaces)
              (behaviour_ws .>> (pstring "}"))
              createComponent
        
    let modelFile = comp_ws
