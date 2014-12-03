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


module internal SafetySharp.Internal.ParseSCM

    open FParsec
    open SafetySharp.Internal.SafetyComponentModel
    
    [<RequireQualifiedAccess>]
    type IdentifierType =
        | Field
        | Var
        | Fault
        | Comp
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
        PositionMap : (System.Collections.Immutable.ImmutableDictionary<obj,FParsec.Position>)
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
            static member freshPositionMap =
                let comparer = { 
                    new System.Collections.Generic.IEqualityComparer<obj> with
                        member this.Equals (symbol1, symbol2) = 
                            obj.ReferenceEquals (symbol1, symbol2)
                        member this.GetHashCode symbol =
                            System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode symbol
                }                
                System.Collections.Immutable.ImmutableDictionary.Create<obj,FParsec.Position> comparer

            static member initialUserState =
                {
                    UserState.IdentifiersComponentScope = UserState.freshScope;
                    UserState.IdentifiersComponentScopeStack = [];
                    UserState.IdentifiersCallScope = UserState.freshScope;
                    UserState.IdentifiersCallScopeStack = [];
                    UserState.PositionMap = UserState.freshPositionMap;
                }

            member us.addPositionOfNode (pos:FParsec.Position) (node:obj) : UserState =
                System.Console.Out.WriteLine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode node)
                System.Console.Out.WriteLine(node)
                System.Console.Out.WriteLine(pos)
                System.Console.Out.WriteLine("--")
                { us with
                    UserState.PositionMap = us.PositionMap.Add (node,pos)
                }
    
    type GuardedCommandClause = Expr * Stm


    //these are overwritten variants, which save the position of the parsed identifier into a map
    (*let (.>>) p1 p2 =
        p1 >>= fun x -> p2 >>% x

    let (>>.) p1 p2 =
        p1 >>= fun _ -> p2

    let (.>>.) p1 p2 =
        p1 >>= fun a ->
        p2 >>= fun b -> preturn (a, b)
    *)

    let (>>%) p x : Parser<_,UserState> =
        p >>=
            (fun _ stream ->
                let resultNode = x
                let positionEnd = stream.Position
                //stream.UserState <- stream.UserState.addPositionOfNode positionEnd (resultNode:> obj)
                preturn x stream
                )

    let (|>>) p f : Parser<_,UserState> =
        p >>= (fun x stream ->
                let resultNode = (f x)
                let position = stream.Position
                stream.UserState <- stream.UserState.addPositionOfNode position (resultNode:> obj)
                preturn resultNode stream
                )
                
    //let stringReturn str result : Parser<_,UserState> =
    //    pstring str >>% result

    let pipe8 p1 p2 p3 p4 p5 p6 p7 p8 f =
        pipe4 p1 p2 p3 (tuple5 p4 p5 p6 p7 p8)
            (fun x1 x2 x3 (x4, x5, x6, x7, x8) -> f x1 x2 x3 x4 x5 x6 x7 x8)
                        

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
    
    let faultIdDecl : Parser<_,UserState> =
        parseIdentifierDecl Scope.Component IdentifierType.Fault |>> Fault.Fault
    let faultIdInst : Parser<_,UserState> =
        parseIdentifierInst IdentifierType.Fault |>> Fault.Fault

    let compIdDecl : Parser<_,UserState> =
        parseIdentifierDecl Scope.Component IdentifierType.Comp |>> Comp.Comp
    let compIdInst : Parser<_,UserState> =
        parseIdentifierInst IdentifierType.Comp |>> Comp.Comp

    // parsers with space afterwards
    let pstring_ws s : Parser<_,UserState> =
        pstring s .>> spaces
    let pstring_ws1 s : Parser<_,UserState> =
        pstring s .>> spaces1
    let boolVal_ws = boolVal .>> spaces
    let numberVal_ws = numberVal .>> spaces
    let value_ws = value .>> spaces
    let varIdDecl_ws = varIdDecl .>> spaces
    let varIdInst_ws = varIdInst .>> spaces
    let fieldIdDecl_ws = fieldIdDecl .>> spaces
    let fieldIdInst_ws = fieldIdInst .>> spaces
    let reqPortId_ws = reqPortId .>> spaces
    let provPortId_ws = provPortId .>> spaces
    let faultIdDecl_ws = faultIdDecl .>> spaces
    let faultIdInst_ws = faultIdInst .>> spaces
    let compIdDecl_ws = compIdDecl .>> spaces
    let compIdInst_ws = compIdInst .>> spaces
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
        opp.AddOperator(InfixOperator("-"   , spaces .>> notFollowedByString ">" , 4, Associativity.Left, fun e1 e2 -> BExpr(e1, BOp.Subtract, e2)))
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

    let param_ws =
        let inoutParam = attempt (pstring_ws1 "inout") >>. varIdInst_ws |>> Param.InOutParam
        let exprParam = attempt expression_ws |>> Param.ExprParam
        inoutParam <|> exprParam
    let params_ws = sepBy (param_ws) (pstring_ws ",")

    do guardedCommandClauseRef :=
       tuple2 (expression_ws .>> (pstring_ws "=>") .>> (pstring_ws "{") )
              (statement_ws .>> (pstring_ws "}"))
        
    do statementRef :=
        let parseVariableAssignment =
            attempt (tuple2 (varIdInst_ws .>> (pstring_ws ":="))
                            (expression .>> (pstring_ws ";")) |>> Stm.AssignVar)
        let parseFieldAssignment =
            attempt (tuple2 (fieldIdInst_ws .>> (pstring_ws ":="))
                            (expression .>> (pstring_ws ";")) |>> Stm.AssignField)
        let parseFaultAssignment =
            // note: should only appear in a FaultDecl (fault {})
            attempt (tuple2 (faultIdInst_ws .>> (pstring_ws ":="))
                            (expression .>> (pstring_ws ";")) |>> Stm.AssignFault)
        let parseBlock =
            attempt (pstring_ws "{") >>. many statement_ws .>> (pstring_ws "}") |>> Stm.Block
        let parseChoice =
            attempt (pstring_ws "choice") >>. (pstring_ws "{") >>.
                    ((sepBy (guardedCommandClause_ws) spaces) |>> Stm.Choice ) .>>
                    (pstring_ws "}")
        let parsePortCall =
            attempt (tuple2 (reqPortId_ws .>> parentOpen_ws)
                            (params_ws .>> parentClose_ws .>>  (pstring_ws ";")) |>> Stm.CallPort)
        let parseStepComp =
            attempt ((pstring_ws1 "step") >>. compIdInst_ws .>>  (pstring_ws ";") ) |>> Stm.StepComp
        let parseStepFault =
            attempt ((pstring_ws1 "step") >>. faultIdInst_ws .>>  (pstring_ws ";") ) |>> Stm.StepFault
            
        let allKindsOfStatements =
            parseVariableAssignment <|>
            parseFieldAssignment <|>
            parseFaultAssignment <|>
            parseBlock <|>
            parseChoice <|>
            parsePortCall <|>
            parseStepComp <|>
            parseStepFault
        allKindsOfStatements
        
        
    let type_ws =
        let boolType = stringReturn "bool" Type.BoolType
        let intType = stringReturn "int"  Type.IntType
        (boolType <|> intType) .>> spaces

    let type_ws1 =
        let boolType = stringReturn "bool" Type.BoolType
        let intType = stringReturn "int"  Type.IntType
        (boolType <|> intType) .>> spaces1
    
    let varDecl1_ws : Parser<_,UserState> =
        let createVarDecl var _type =
            {
                VarDecl.Var = var ;
                VarDecl.Type = _type ;
            }
        pipe2 (varIdDecl_ws .>> (pstring_ws ":" )) 
              (type_ws)
              createVarDecl

    let varDecls1_ws =
        sepBy varDecl1_ws (pstring_ws ",")

    let paramDecl_ws : Parser<_,UserState> =
        let createParamDecl varDecl dir =
            {
                ParamDecl.Var = varDecl
                ParamDecl.Dir = dir ;
            }
        let inParam_ws =
            attempt varDecl1_ws |>> (fun varDecl -> createParamDecl varDecl ParamDir.In)
        let inoutParam_ws =
            attempt ((pstring_ws1 "inout") >>. varDecl1_ws) |>> (fun varDecl -> createParamDecl varDecl ParamDir.InOut)
        inParam_ws <|> inoutParam_ws

    let paramDecls_ws =
        sepBy paramDecl_ws (pstring_ws ",")
    
    
    let varDecl2_ws : Parser<_,UserState> =
        let createVarDecl _type var=
            {
                VarDecl.Var = var ;
                VarDecl.Type = _type ;
            }
        pipe2 (type_ws1)
              (varIdDecl_ws ) 
              createVarDecl

    let varDecls2_ws =
        sepBy varDecl2_ws (pstring_ws ";")

    let behaviorDecl_ws  =
        let createBehavior locals body =
            {
                BehaviorDecl.Locals = locals ;
                BehaviorDecl.Body = body;
            }
        pipe2 ((pstring_ws "locals") >>. (pstring_ws "{") >>. varDecls2_ws .>> (pstring_ws "}"))
              (many statement_ws |>> Stm.Block)
              createBehavior
    
    let faultExpr_ws  : Parser<_,UserState> =
        let faultExprTerminal_ws =
            (faultIdInst_ws |>> (fun field -> ("yes", field ))) <|>
            ((pstring_ws "!") >>. faultIdInst_ws |>>  (fun field -> ("no", field)))
        let refurbishResult (faults:(string*Fault) list) : FaultExpr =
            let mustAppear =
                faults |> List.filter ( fun (whichList,_) -> whichList="yes")
                       |> List.map (fun (_,fault) -> fault)
            let mustNotAppear =
                faults |> List.filter ( fun (whichList,_) -> whichList="no")
                       |> List.map (fun (_,fault) -> fault)
            {
                FaultExpr.MustAppear = mustAppear;
                FaultExpr.MustNotAppear = mustNotAppear;
            }
        let faultExprComplete =
            sepBy1 faultExprTerminal_ws (pstring_ws "&&") |>> refurbishResult
        faultExprComplete


    let faultExprOpt_ws =
        let foundSomething = (pstring_ws "[") >>. faultExpr_ws .>> (pstring_ws "]")
        ((attempt foundSomething) |>> Some) <|>
        (spaces >>% None)
     

    let stepDecl =
        let createStep faultExpr behavior =
            {
                StepDecl.FaultExpr = faultExpr;
                StepDecl.Behavior = behavior;
            }
        pipe2 (faultExprOpt_ws .>> (pstring_ws "step") .>> (pstring_ws "{") .>> pushUserStateCallStack)
              (behaviorDecl_ws .>> (pstring "}") .>> popUserStateCallStack)
              createStep

    let stepDecl_ws = stepDecl .>> spaces
    
    let (comp:Parser<_,UserState>), compRef = createParserForwardedToRef()
    let comp_ws = comp .>> spaces

    let typedFieldDecl_ws : Parser<_,UserState> =
        let createFieldDecl var fieldType (init:Val list) =
            {
                FieldDecl.Field = var ;
                FieldDecl.Type = fieldType;
                FieldDecl.Init = init ;
            }
        attempt (pipe3 (fieldIdDecl_ws .>> (pstring_ws ":"))
                       (type_ws1)
                       (many1 value_ws)
                       createFieldDecl)

    let faultDecls_ws : Parser<_,UserState> =
        let createFaultDecl faultId behavior =
            {
                FaultDecl.Fault = faultId;
                FaultDecl.Step = behavior;
            }
        pipe2 ((pstring_ws1 "fault") >>. faultIdDecl_ws)
              ( (pstring_ws "{") >>. pushUserStateCallStack >>. behaviorDecl_ws .>> (pstring "}") .>> popUserStateCallStack)
              createFaultDecl

    let reqPortDecl_ws : Parser<_,UserState> =
        let createReqPortDecl name parms =
            {
                ReqPortDecl.ReqPort = name;
                ReqPortDecl.Params = parms ;
            }
        attempt (pipe2 (reqPortId_ws .>> (pstring_ws "(") .>> pushUserStateCallStack)
                       (paramDecls_ws .>> parentClose_ws .>> popUserStateCallStack)
                       createReqPortDecl)

    let provPortDecl_ws : Parser<_,UserState> =
        let createProvPortDecl faultExpr name parms behavior =
            {
                ProvPortDecl.ProvPort = name;
                ProvPortDecl.Params = parms ;
                ProvPortDecl.Behavior = behavior;
                ProvPortDecl.FaultExpr = faultExpr;
            }
        attempt (pipe4 (faultExprOpt_ws)
                       (provPortId_ws .>> (pstring_ws "(") .>> pushUserStateCallStack)
                       (paramDecls_ws .>> parentClose_ws .>> (pstring_ws "{"))
                       (behaviorDecl_ws .>> (pstring_ws "}") .>> popUserStateCallStack)
                       createProvPortDecl)
                                                  
    let binding_ws : Parser<_,UserState> =
        let bindingsrc_ws =
            let createProvPortSame srcPort = {BndSrc.Comp = None; BndSrc.ProvPort=srcPort}
            let createProvPortChild (comp,srcPort) = {BndSrc.Comp = Some(comp); BndSrc.ProvPort=srcPort}
            let samecmp_ws = provPortId_ws |>> createProvPortSame
            let childcmp_ws = attempt (compIdInst_ws .>>. (pstring_ws "." >>. provPortId_ws)) |>> createProvPortChild
            samecmp_ws <|> childcmp_ws

        let bindingtarget_ws =
            let createReqPortSame targetPort = {BndTarget.Comp = None; BndTarget.ReqPort=targetPort}
            let createReqPortChild (comp,targetPort) = {BndTarget.Comp = Some(comp); BndTarget.ReqPort=targetPort}
            let samecmp_ws = reqPortId_ws |>> createReqPortSame
            let childcmp_ws = attempt (compIdInst_ws .>>. (pstring_ws "." >>. reqPortId_ws)) |>> createReqPortChild
            samecmp_ws <|> childcmp_ws
        
        let instantbinding_ws =
            let createBinding (req) (prov) =
                {
                    BndDecl.Target = req;
                    BndDecl.Source = prov;
                    BndDecl.Kind = BndKind.Instantaneous;
                }
            attempt (pipe2 (bindingtarget_ws .>> (pstring_ws "=").>> (pstring_ws "instantly"))
                           (bindingsrc_ws)
                           createBinding)
           
        let delayedbinding_ws =
            let createBinding (req) (prov) =
                {
                    BndDecl.Target = req;
                    BndDecl.Source = prov;
                    BndDecl.Kind = BndKind.Instantaneous;
                }
            attempt (pipe2 (bindingtarget_ws .>> (pstring_ws "=").>> (pstring_ws "delayed"))
                           (bindingsrc_ws)
                           createBinding)

        instantbinding_ws <|> delayedbinding_ws

        

    do compRef :=
        let createComponent comp subcomp fields faults reqPorts provPorts bindings steps =
            {
                CompDecl.Comp = comp;
                CompDecl.Subs = subcomp;
                CompDecl.Fields = fields;
                CompDecl.Faults = [];
                CompDecl.ReqPorts = reqPorts;
                CompDecl.ProvPorts = provPorts;
                CompDecl.Bindings = bindings;
                CompDecl.Steps = steps;
            }
        pipe8 ((pstring_ws1 "component") >>. compIdDecl_ws .>> (pstring_ws "{") .>> pushUserStateComponentStack)
              (many comp_ws)
              (many typedFieldDecl_ws)
              (many faultDecls_ws)
              (many reqPortDecl_ws)
              (many provPortDecl_ws)
              (many binding_ws)
              (many stepDecl_ws .>> (pstring "}") .>> popUserStateComponentStack)
              createComponent
        
    let modelFile = comp_ws
