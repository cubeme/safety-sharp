﻿// The MIT License (MIT)
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
        
    [<RequireQualifiedAccess>]
    type Scope =
        | Component
        | Call


    type UserState = {
        IdentifiersComponentScope : Map<string,IdentifierType> ;
        IdentifiersComponentScopeStack : (Map<string,IdentifierType>) list;
        IdentifiersCallScope : Map<string,IdentifierType> ;
        IdentifiersCallScopeStack : (Map<string,IdentifierType>) list;
        PositionMap : (System.Collections.Immutable.ImmutableDictionary<obj,int*int>)
    }
        with
            member us.IsIdentifierOfType str (id_type:IdentifierType) =
                if us.IdentifiersComponentScope.ContainsKey str && (us.IdentifiersComponentScope.Item str) = id_type then
                    true
                elif us.IdentifiersCallScope.ContainsKey str && (us.IdentifiersCallScope.Item str) = id_type then
                    true
                else
                    false
            member us.pushComponentScope : UserState =
                { us with
                    UserState.IdentifiersComponentScope = UserState.freshScope ;
                    UserState.IdentifiersComponentScopeStack = us.IdentifiersComponentScope :: us.IdentifiersComponentScopeStack ;
                }
                
            member us.popComponentScope : UserState =
                { us with
                    UserState.IdentifiersComponentScope = us.IdentifiersComponentScopeStack.Head ;
                    UserState.IdentifiersComponentScopeStack = us.IdentifiersComponentScopeStack.Tail ;
                }                
            member us.addToComponentScope (identifier:string) (id_type:IdentifierType) : UserState =
                { us with
                    UserState.IdentifiersComponentScope = us.IdentifiersComponentScope.Add(identifier, id_type) ;
                }
                
            member us.pushCallScope : UserState =
                { us with
                    UserState.IdentifiersCallScope = UserState.freshScope ;
                    UserState.IdentifiersCallScopeStack = us.IdentifiersCallScope :: us.IdentifiersCallScopeStack ;
                }
                
            member us.popCallScope : UserState =
                { us with
                    UserState.IdentifiersCallScope = us.IdentifiersCallScopeStack.Head ;
                    UserState.IdentifiersCallScopeStack = us.IdentifiersCallScopeStack.Tail ;
                }

            member us.addToCallScope (identifier:string) (id_type:IdentifierType) : UserState =
                { us with
                    UserState.IdentifiersCallScope = us.IdentifiersCallScope.Add(identifier, id_type) ;
                }

            member us.addToScope (identifier:string) (id_type:IdentifierType) (scope:Scope) : UserState =
                match scope with
                    | Scope.Call -> us.addToCallScope identifier id_type
                    | Scope.Component -> us.addToComponentScope identifier id_type
            
            static member freshScope =
                 Map.empty<string,IdentifierType>;                
            static member initialUserState =
                {
                    UserState.IdentifiersComponentScope = UserState.freshScope;
                    UserState.IdentifiersComponentScopeStack = [];
                    UserState.IdentifiersCallScope = UserState.freshScope;
                    UserState.IdentifiersCallScopeStack = [];
                    UserState.PositionMap = System.Collections.Immutable.ImmutableDictionary<obj,int*int>.Empty;
                }
    
    type GuardedCommandClause = Expr * Stm


    //these are overwritten variants, which save the position of the parsed identifier into a map
    let (.>>) p1 p2 =
        p1 >>= fun x -> p2 >>% x

    let (>>.) p1 p2 =
        p1 >>= fun _ -> p2

    let (.>>.) p1 p2 =
        p1 >>= fun a ->
        p2 >>= fun b -> preturn (a, b)

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
        
    let parseIdentifierDecl (scope:Scope) (id_type:IdentifierType) : Parser<_,UserState> =        
        let parseIdentifier = identifier (IdentifierOptions())
        fun stream ->
            let identifier = (parseIdentifier stream)
            if identifier.Status = ReplyStatus.Ok then
                stream.UserState <- stream.UserState.addToScope identifier.Result id_type scope
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
    
    // TODO: write test, which confuses the state (subcomponent with field "x" , which was a localVar of a behaviour)
    let pushUserStateComponentStack : Parser<_,UserState> =
        updateUserState (fun userstate -> userstate.pushComponentScope)
     
    let popUserStateComponentStack : Parser<_,UserState> =
        updateUserState (fun userstate -> userstate.popComponentScope)

    let pushUserStateCallStack : Parser<_,UserState> =
        updateUserState (fun userstate -> userstate.pushCallScope)
     
    let popUserStateCallStack : Parser<_,UserState> =
        updateUserState (fun userstate -> userstate.popCallScope)

    // parse identifier of variables, fields, ports and components
    let varIdDecl: Parser<_,UserState> =
        parseIdentifierDecl Scope.Call IdentifierType.Var |>> Var.Var
    let varIdInst: Parser<_,UserState> =
        parseIdentifierInst IdentifierType.Var |>> Var.Var
    

    let fieldIdDecl: Parser<_,UserState> =
        parseIdentifierDecl Scope.Component IdentifierType.Field |>> Field.Field
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
            attempt (tuple3 (reqPortId_ws .>> parentOpen_ws)
                            (expressions_ws .>> (pstring_ws ";"))
                            (varIdInsts_ws .>> parentClose_ws)) |>> Stm.CallPort
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

    let typedVarDecls_ws =
        sepBy typedVarDecl_ws (pstring_ws ",")
    
    let varsAndCode_ws = 
        tuple2 (typedVarDecls_ws .>> (pstring_ws ".")) (statement_ws)
    
    let behaviour =
        (pstring_ws "behaviour") >>. (pstring_ws "{") .>> pushUserStateCallStack >>. varsAndCode_ws .>> (pstring "}") .>> popUserStateCallStack

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

    //getSensorValue1R r( ; sensorValueInout : int )
    let reqPortDecl_ws : Parser<_,UserState> =
        let extractTypes (vars:VarSym list) = vars |> List.map (fun var -> var.Type)
        let createReqPortSym name inParms outParms =
            {
                ReqPortSym.ReqPort = name;
                ReqPortSym.InParams = extractTypes inParms ;
                ReqPortSym.InOutParams = extractTypes outParms ;
            }
        attempt (pipe3 (reqPortId_ws .>> (pstring_ws "r(") .>> pushUserStateCallStack)
                       (typedVarDecls_ws .>> (pstring_ws ";"))
                       (typedVarDecls_ws .>> parentClose_ws .>> popUserStateCallStack)
                       createReqPortSym)

    let provPortDecl_ws : Parser<_,UserState> =
        let extractTypes (vars:VarSym list) = vars |> List.map (fun var -> var.Type)
        let createProvPortSym name inParms outParms (locals,stm) =
            {
                ProvPortSym.ProvPort = name;
                ProvPortSym.InParams = inParms ;
                ProvPortSym.InOutParams = outParms ;
                ProvPortSym.Locals = locals;
                ProvPortSym.Stm = stm;
            }
        attempt (pipe4 (provPortId_ws .>> (pstring_ws "p(") .>> pushUserStateCallStack)
                       (typedVarDecls_ws .>> (pstring_ws ";"))
                       (typedVarDecls_ws .>> parentClose_ws .>> (pstring_ws "{"))
                       (varsAndCode_ws .>> (pstring_ws "}") .>> popUserStateCallStack)
                       createProvPortSym)
                                                  
    let binding_ws : Parser<_,UserState> =
        let bindingsrc_ws =
            let samecmp_ws = provPortId_ws |>> BndSrc.SameCmp
            let childcmp_ws = attempt (compId_ws .>>. (pstring_ws "." >>. provPortId_ws)) |>> BndSrc.ChildCmp
            samecmp_ws <|> childcmp_ws

        let bindingtarget_ws =
            let samecmp_ws = reqPortId_ws |>> BndTarget.SameCmp
            let childcmp_ws = attempt (compId_ws .>>. (pstring_ws "." >>. reqPortId_ws)) |>> BndTarget.ChildCmp
            samecmp_ws <|> childcmp_ws
        
        let instantbinding_ws =
            let createBinding (req) (prov) =
                {
                    BindingSym.ReqPort = req;
                    BindingSym.ProvPort = prov;
                    BindingSym.Type = BndType.Instantaneous;
                }
            attempt (pipe2 (bindingtarget_ws .>> (pstring_ws "<-i-")) (bindingsrc_ws) createBinding)
           
        let delayedbinding_ws =
            let createBinding (req) (prov) =
                {
                    BindingSym.ReqPort = req;
                    BindingSym.ProvPort = prov;
                    BindingSym.Type = BndType.Instantaneous;
                }
            attempt (pipe2 (bindingtarget_ws .>> (pstring_ws "<-d-")) (bindingsrc_ws) createBinding)

        instantbinding_ws <|> delayedbinding_ws

        

    do compRef :=
        let createComponent comp subcomp fields reqPorts provPorts bindings (locals,stm) =
            {
                CompSym.Comp = comp;
                CompSym.Subcomp = subcomp;
                CompSym.Fields = fields;
                CompSym.ReqPorts = reqPorts;
                CompSym.ProvPorts = provPorts;
                CompSym.Bindings = bindings;
                CompSym.Locals = locals;
                CompSym.Stm = stm;
            }
        pipe7 ((pstring "component") >>. spaces1 >>. compId_ws .>> (pstring_ws "{") .>> pushUserStateComponentStack)
              (many comp_ws)
              (many typedFieldDecl_ws)
              (many reqPortDecl_ws)
              (many provPortDecl_ws)
              (many binding_ws)
              (behaviour_ws .>> (pstring "}") .>> popUserStateComponentStack)
              createComponent
        
    let modelFile = comp_ws
