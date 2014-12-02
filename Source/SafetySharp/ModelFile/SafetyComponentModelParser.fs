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

namespace SafetySharp.Internal.SafetyComponentModel.Parser


module internal ParseSCM =

    open FParsec
    open SafetySharp.Internal.SafetyComponentModel
    
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
        let parseChoice =
            attempt (sepBy (guardedCommandClause_ws) (pstring_ws "|||")) |>> Stm.Choice
        let parseFieldAssignment =
            attempt (fieldIdInst_ws .>>. (pstring_ws ":=" >>. expression)) |>> Stm.AssignField
        let parseVariableAssignment =
            attempt (varIdInst_ws .>>. (pstring_ws ":=" >>. expression)) |>> Stm.AssignVar
        let parsePortCall =
            attempt (tuple3 (reqPortId_ws .>> parentOpen_ws)
                            (expressions_ws .>> (pstring_ws ";"))
                            (varIdInsts_ws .>> parentClose_ws)) |>> (fun (a,b,c) -> (a,b) |> Stm.CallPort) //TODO
        let parseBehCall =
            attempt (compId_ws.>> parentOpen_ws .>> parentClose_ws) |>> Stm.StepComp


        // a; b; c == (a ; b) ; c  //left associative (in semantics)
        let allExceptSeq =
            parseChoice <|>
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
        let createVarDecl var _type =
            {
                VarDecl.Var = var ;
                VarDecl.Type = _type ;
            }
        pipe2 (varIdDecl_ws .>> (pstring_ws ":" )) 
              (type_ws)
              createVarDecl

    let typedVarDecls_ws =
        sepBy typedVarDecl_ws (pstring_ws ",")


    let paramDecl_ws : Parser<_,UserState> =
        let createParamDecl var _type dir =
            {
                ParamDecl.Var =
                    {
                        VarDecl.Var = var;
                        VarDecl.Type = _type;
                    }
                ParamDecl.Dir = ParamDir.In ;
            }
        pipe3 (varIdDecl_ws .>> (pstring_ws ":" )) 
              (type_ws)
              (spaces)
              createParamDecl

    let paramDecls_ws =
        sepBy paramDecl_ws (pstring_ws ",")
    
    let behaviorDecl_ws  =
        let createBehavior locals body =
            {
                BehaviorDecl.Locals = locals ;
                BehaviorDecl.Body = body;
            }
        pipe2 (typedVarDecls_ws .>> (pstring_ws "."))
              (statement_ws)
              createBehavior
    
    let step =
        (pstring_ws "behaviour") >>. (pstring_ws "{") .>> pushUserStateCallStack >>. behaviorDecl_ws .>> (pstring "}") .>> popUserStateCallStack

    let step_ws = step .>> spaces
    
    let (comp:Parser<_,UserState>), compRef = createParserForwardedToRef()
    let comp_ws = comp .>> spaces

    let typedFieldDecl_ws : Parser<_,UserState> =
        let createFieldDecl var (init:Val list) =
            let _type = 
                match init.Head with
                    | Val.BoolVal(_) -> Type.BoolType
                    | Val.IntVal(_) -> Type.IntType
            {
                FieldDecl.Field = var ;
                FieldDecl.Type = _type ;
                FieldDecl.Init = init ;
            }
        attempt (pipe2 (fieldIdDecl_ws .>> (pstring_ws "="))
                       (many1 value_ws)
                       createFieldDecl)

    //getSensorValue1R r( ; sensorValueInout : int )
    let reqPortDecl_ws : Parser<_,UserState> =
        //let extractTypes (vars:VarDecl list) = vars |> List.map (fun var -> var.Type)
        let createReqPortDecl name parms = // outParms =
            {
                ReqPortDecl.ReqPort = name;
                ReqPortDecl.Params = parms ;
                //ReqPortDecl.InOutParams = extractTypes outParms ;
            }
        attempt (pipe2 (reqPortId_ws .>> (pstring_ws "r(") .>> pushUserStateCallStack)
                       //(typedVarDecls_ws )//.>> (pstring_ws ";"))
                       (paramDecls_ws .>> parentClose_ws .>> popUserStateCallStack)
                       createReqPortDecl)

    let provPortDecl_ws : Parser<_,UserState> =
        let extractTypes (vars:VarDecl list) = vars |> List.map (fun var -> var.Type)
        let createProvPortDecl name parms behavior =
            {
                ProvPortDecl.ProvPort = name;
                ProvPortDecl.Params = parms ;
                ProvPortDecl.Behavior = behavior;
                ProvPortDecl.FaultExpr = None;
            }
        attempt (pipe3 (provPortId_ws .>> (pstring_ws "p(") .>> pushUserStateCallStack)
                       (paramDecls_ws .>> parentClose_ws .>> (pstring_ws "{"))
                       (behaviorDecl_ws .>> (pstring_ws "}") .>> popUserStateCallStack)
                       createProvPortDecl)
                                                  
    let binding_ws : Parser<_,UserState> =
        let bindingsrc_ws =
            let createProvPortSame srcPort = {BndSrc.Comp = None; BndSrc.ProvPort=srcPort}
            let createProvPortChild (comp,srcPort) = {BndSrc.Comp = Some(comp); BndSrc.ProvPort=srcPort}
            let samecmp_ws = provPortId_ws |>> createProvPortSame
            let childcmp_ws = attempt (compId_ws .>>. (pstring_ws "." >>. provPortId_ws)) |>> createProvPortChild
            samecmp_ws <|> childcmp_ws

        let bindingtarget_ws =
            let createReqPortSame targetPort = {BndTarget.Comp = None; BndTarget.ReqPort=targetPort}
            let createReqPortChild (comp,targetPort) = {BndTarget.Comp = Some(comp); BndTarget.ReqPort=targetPort}
            let samecmp_ws = reqPortId_ws |>> createReqPortSame
            let childcmp_ws = attempt (compId_ws .>>. (pstring_ws "." >>. reqPortId_ws)) |>> createReqPortChild
            samecmp_ws <|> childcmp_ws
        
        let instantbinding_ws =
            let createBinding (req) (prov) =
                {
                    BndDecl.Target = req;
                    BndDecl.Source = prov;
                    BndDecl.Kind = BndKind.Instantaneous;
                }
            attempt (pipe2 (bindingtarget_ws .>> (pstring_ws "<-i-")) (bindingsrc_ws) createBinding)
           
        let delayedbinding_ws =
            let createBinding (req) (prov) =
                {
                    BndDecl.Target = req;
                    BndDecl.Source = prov;
                    BndDecl.Kind = BndKind.Instantaneous;
                }
            attempt (pipe2 (bindingtarget_ws .>> (pstring_ws "<-d-")) (bindingsrc_ws) createBinding)

        instantbinding_ws <|> delayedbinding_ws

        

    do compRef :=
        let createComponent comp subcomp fields reqPorts provPorts bindings steps =
            {
                CompDecl.Comp = comp;
                CompDecl.Subs = subcomp;
                CompDecl.Fields = fields;
                CompDecl.Faults = [];
                CompDecl.ReqPorts = reqPorts;
                CompDecl.ProvPorts = provPorts;
                CompDecl.Bindings = bindings;
                CompDecl.Steps = [];
            }
        pipe7 ((pstring "component") >>. spaces1 >>. compId_ws .>> (pstring_ws "{") .>> pushUserStateComponentStack)
              (many comp_ws)
              (many typedFieldDecl_ws)
              (many reqPortDecl_ws)
              (many provPortDecl_ws)
              (many binding_ws)
              (step_ws .>> (pstring "}") .>> popUserStateComponentStack)
              createComponent
        
    let modelFile = comp_ws
