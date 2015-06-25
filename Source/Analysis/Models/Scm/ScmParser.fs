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

module internal ScmParser =
    open FParsec
    open SafetySharp.Models.Scm
    open SafetySharp.GenericParsers
    
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
        CurrentComponentLocation : CompPath ;
        IdentifiersComponentScope : Map<string,IdentifierType> ; // identifiers in current scope
        IdentifiersComponentScopeStack : (Map<string,IdentifierType>) list; // (identifiers in current scope) :: (identifiers in parent scope) :: ... :: []        
        IdentifiersComponentLocationScope : Map<CompPath*string,IdentifierType> ; // CompPath is subgrandchild::subchild. Does not contain the name of the current component (makes code easier). Only Fields and Faults
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
            member us.IsLocatedIdentifierOfType (location,str) (id_type:IdentifierType) =
                // we are not interested in the name of the current node, we just check, if the name is correct
                let reverseLocation = location |> List.rev
                let currentComponent = reverseLocation |> List.head
                let location =
                    // new location without the current node
                    reverseLocation |> List.tail |> List.rev
                if currentComponent <> us.CurrentComponentLocation.Head then
                    false // wrong location
                else if us.IdentifiersComponentLocationScope.ContainsKey (location,str) && (us.IdentifiersComponentLocationScope.Item (location,str)) = id_type then
                    true
                else
                    false
            member us.pushComponentScope (compName:Comp) : UserState =
                { us with
                    UserState.CurrentComponentLocation = compName::us.CurrentComponentLocation;
                    UserState.IdentifiersComponentScope = UserState.freshScope ;
                    UserState.IdentifiersComponentScopeStack = us.IdentifiersComponentScope :: us.IdentifiersComponentScopeStack ;
                    UserState.IdentifiersComponentLocationScope = Map.empty<CompPath*string,IdentifierType>;
                }
                
            member us.popComponentScope : UserState =
                { us with
                    UserState.CurrentComponentLocation = us.CurrentComponentLocation.Tail;
                    UserState.IdentifiersComponentScope = us.IdentifiersComponentScopeStack.Head ;
                    UserState.IdentifiersComponentScopeStack = us.IdentifiersComponentScopeStack.Tail ;
                    UserState.IdentifiersComponentLocationScope =
                        // add to every entry the name of the current component after popping
                        us.IdentifiersComponentLocationScope |> Map.toList
                                                             |> List.map (fun ((location,string),id_type) -> ((location @ [us.CurrentComponentLocation.Head] ,string),id_type) )
                                                             |> Map.ofList
                }                
            member us.addToComponentScope (identifier:string) (id_type:IdentifierType) : UserState =
                { us with
                    UserState.IdentifiersComponentScope = us.IdentifiersComponentScope.Add(identifier, id_type) ;
                    UserState.IdentifiersComponentLocationScope = us.IdentifiersComponentLocationScope.Add ( ([],identifier),id_type)
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
                    UserState.CurrentComponentLocation = [];
                    UserState.IdentifiersComponentScope = UserState.freshScope;
                    UserState.IdentifiersComponentScopeStack = [];
                    UserState.IdentifiersComponentLocationScope = Map.empty<CompPath*string,IdentifierType>;
                    UserState.IdentifiersCallScope = UserState.freshScope;
                    UserState.IdentifiersCallScopeStack = [];
                    UserState.PositionMap = UserState.freshPositionMap;
                }

            member us.addPositionOfNode (pos:FParsec.Position) (node:obj) : UserState =
                (*
                System.Console.Out.WriteLine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode node)
                System.Console.Out.WriteLine(node)
                System.Console.Out.WriteLine(pos)
                System.Console.Out.WriteLine("--")
                *)
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

    let (oldPipeTo) = (|>>) // does not something into userstate
    
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
            
    let pipe9 p1 p2 p3 p4 p5 p6 p7 p8 p9 f =
        pipe5 p1 p2 p3 p4 (tuple5 p5 p6 p7 p8 p9)
            (fun x1 x2 x3 x4 (x5, x6, x7, x8, x9) -> f x1 x2 x3 x4 x5 x6 x7 x8 x9)

    let isIdentifierStart (c:char) : bool =
        (((c>'a')&&(c<'z')) || ((c>'A')&&(c<'Z')))
        
    let parseIdentifier<'us> : Parser<string,'us> = identifier (IdentifierOptions())

    // parses the Boolean constants true or false, yielding a Boolean AST node
    let trueKeyword<'us> : Parser<_,'us> =
        stringReturn "true" (Val.BoolVal true)
    let falseKeyword<'us>  : Parser<_,'us> =
        stringReturn "false" (Val.BoolVal false)

    // parses the Boolean constants, but not, e.g., truee or false1, 
    let boolVal<'us> : Parser<_,'us> =
        let isIdentifierChar c = isLetter c || isDigit c || c = '_'
        (trueKeyword <|> falseKeyword) .>>? (notFollowedBy (many1Satisfy isIdentifierChar))

    // parses a number

    let numberVal<'us> : Parser<_,'us> =
        oldPipeTo (many1Satisfy isDigit)
                  ( fun value -> (bigint.Parse value |> int32 |> Val.IntVal ))
        
    let realVal<'us> : Parser<_,'us> =
        let decimalToVal (dec:string) =
            System.Convert.ToDouble(dec) |> Val.RealVal
        oldPipeTo parseDecimal decimalToVal
        
    let value<'us> : Parser<_,'us> =
        boolVal <|> realVal <|> numberVal        
        
    let probVal<'us> : Parser<_,'us> =
        let decimalToVal (dec:string) =
            System.Convert.ToDouble(dec,System.Globalization.CultureInfo.InvariantCulture) |> Val.ProbVal
        oldPipeTo parseDecimal decimalToVal

    let parseIdentifierDecl (scope:Scope) (id_type:IdentifierType) : Parser<_,UserState> =
        fun stream ->
            let identifier = (parseIdentifier stream)
            if identifier.Status = ReplyStatus.Ok then
                stream.UserState <- stream.UserState.addToScope identifier.Result id_type scope
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
                                
    let comppath_dot : Parser<_,UserState> =
        // TODO: could check, if path is correct
        oldPipeTo (many1 (attempt (parseIdentifier |>> Comp.Comp .>> pstring "." )))
                  List.rev
                      
    let parseLocatedIdentifierInst (id_type:IdentifierType) : Parser<_,UserState> =
        fun stream ->
            let locationIdentifierReply = (comppath_dot .>>. parseIdentifier) stream
            //let identifier = (parseIdentifier stream)
            if locationIdentifierReply.Status = ReplyStatus.Ok then
                let (location,identifier) = locationIdentifierReply.Result
                if stream.UserState.IsLocatedIdentifierOfType (location,identifier) id_type then
                    Reply(locationIdentifierReply.Status,(location,identifier),locationIdentifierReply.Error)
                else
                    let error = messageError (sprintf "Identifier '%s' has not been declared in path %s or the kind of access is wrong" identifier (location |> List.rev |> List.map (fun (Comp(c)) -> c) |> String.concat ".") )
                    Reply(ReplyStatus.Error,mergeErrors locationIdentifierReply.Error error)
            else
                Reply(locationIdentifierReply.Status,locationIdentifierReply.Error)
                     
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
        
    let compIdInst : Parser<_,UserState> =
        parseIdentifierInst IdentifierType.Comp |>> Comp.Comp
    let declareComponentName_and_pushUserStateComponentStack : Parser<_,UserState> = //name of current Component is parsed
        fun stream ->
            let identifierReply = (parseIdentifier stream)
            if identifierReply.Status = ReplyStatus.Ok then
                let comp = Comp(identifierReply.Result)
                stream.UserState <- stream.UserState.addToComponentScope (identifierReply.Result) IdentifierType.Comp // add component to _old_ scope
                stream.UserState <- stream.UserState.pushComponentScope comp
                Reply(identifierReply.Status,comp,identifierReply.Error)
            else
                Reply(identifierReply.Status,identifierReply.Error)

        
    let locatedFieldInst : Parser<_,UserState> =
        parseLocatedIdentifierInst IdentifierType.Field |>> (fun (loc,str) -> (loc,Field(str)))

    let locatedFaultInst : Parser<_,UserState> =
        parseLocatedIdentifierInst IdentifierType.Fault |>> (fun (loc,str) -> (loc,Fault.Fault(str)))

    // parsers with space afterwards
    let pstring_ws s : Parser<_,UserState> =
        pstring s .>> spaces
    let pstring_ws1 s : Parser<_,UserState> =
        pstring s .>> spaces1
    let boolVal_ws<'us> = boolVal<'us> .>> spaces
    let numberVal_ws<'us> = numberVal<'us> .>> spaces
    let value_ws<'us> = value<'us> .>> spaces
    let probVal_ws<'us> = probVal<'us> .>> spaces
    let parseIdentifier_ws = parseIdentifier .>> spaces
    let varIdDecl_ws = varIdDecl .>> spaces
    let varIdInst_ws = varIdInst .>> spaces
    let fieldIdDecl_ws = fieldIdDecl .>> spaces
    let fieldIdInst_ws = fieldIdInst .>> spaces
    let reqPortId_ws = reqPortId .>> spaces
    let provPortId_ws = provPortId .>> spaces
    let faultIdDecl_ws = faultIdDecl .>> spaces
    let faultIdInst_ws = faultIdInst .>> spaces
    let compIdInst_ws = compIdInst .>> spaces
    let declareComponentName_and_pushUserStateComponentStack_ws = declareComponentName_and_pushUserStateComponentStack .>> spaces
    let parentOpen_ws = pstring_ws "("
    let parentClose_ws = pstring_ws ")"
    let locatedFieldInst_ws = locatedFieldInst .>> spaces
    let locatedFaultInst_ws = locatedFaultInst .>> spaces
    
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
            (attempt fieldIdInst_ws |>> Expr.ReadField) <|>
            (attempt varIdInst_ws |>> Expr.ReadVar) <|> 
            (parenExpr_ws)

        opp.ExpressionParser
        
    let (statement:Parser<_,UserState>),statementRef = createParserForwardedToRef()
    
    let expression_ws = expression .>> spaces
    let statement_ws = statement .>> spaces

    let expressions_ws = sepBy expression_ws (pstring_ws ",")
    let varIdInsts_ws = sepBy varIdInst_ws (pstring_ws ",")
    let param_ws =
        let inoutVarParam = attempt ((pstring_ws1 "inout") >>. varIdInst_ws) |>> Param.InOutVarParam
        let inoutFieldParam = attempt ((pstring_ws1 "inout") >>. fieldIdInst_ws) |>> Param.InOutFieldParam
        let exprParam = attempt ((pstring_ws1 "in") >>. expression_ws) |>> Param.ExprParam
        inoutVarParam <|> inoutFieldParam <|> exprParam
    let params_ws = sepBy (param_ws) (pstring_ws ",")
    
    let probability_expression : Parser<_,UserState> =
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
    let (stochasticClause:Parser<_,UserState>),stochasticClauseRef = createParserForwardedToRef()
    let stochasticClause_ws = stochasticClause .>> spaces
    do stochasticClauseRef :=
       tuple2 (probability_expression .>> (pstring_ws "=>") .>> (pstring_ws "{") )
              ((many statement_ws |>> Stm.Block) .>> (pstring_ws "}"))
    
    let (guardedCommandClause:Parser<_,UserState>),guardedCommandClauseRef = createParserForwardedToRef()
    let guardedCommandClause_ws = guardedCommandClause .>> spaces
    do guardedCommandClauseRef :=
       tuple2 (expression_ws .>> (pstring_ws "=>") .>> (pstring_ws "{") )
              ((many statement_ws |>> Stm.Block) .>> (pstring_ws "}"))
        
    do statementRef :=
        let parseVariableAssignment =
            attempt (tuple2 (varIdInst_ws .>> (pstring_ws ":="))
                            (expression_ws .>> (pstring_ws ";")) |>> Stm.AssignVar)
        let parseFieldAssignment =
            attempt (tuple2 (fieldIdInst_ws .>> (pstring_ws ":="))
                            (expression_ws .>> (pstring_ws ";")) |>> Stm.AssignField)
        let parseFaultAssignment =
            // note: should only appear in a FaultDecl (fault {})
            attempt (tuple2 (faultIdInst_ws .>> (pstring_ws ":="))
                            (expression_ws .>> (pstring_ws ";")) |>> Stm.AssignFault)
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
            parseStochastic <|>
            parsePortCall <|>
            parseStepComp <|>
            parseStepFault
        allKindsOfStatements
        

    // parses a hierarchical expression
    let hierarchical_expression : Parser<_,UserState> =
        let oldValueIndicator =      
            //Old Value : '⁻' (U+207B = SUPERSCRIPT MINUS)
            pchar '\u207B'

        let opp = new OperatorPrecedenceParser<_,_,_>()        
        opp.AddOperator(InfixOperator("/"   , spaces , 5, Associativity.Left, fun e1 e2 -> LocExpr.BExpr(e1, BOp.Divide, e2)))
        opp.AddOperator(InfixOperator("*"   , spaces , 5, Associativity.Left, fun e1 e2 -> LocExpr.BExpr(e1, BOp.Multiply, e2)))
        opp.AddOperator(InfixOperator("%"   , spaces , 5, Associativity.Left, fun e1 e2 -> LocExpr.BExpr(e1, BOp.Modulo, e2)))
        // >
        opp.AddOperator(InfixOperator("+"   , spaces , 4, Associativity.Left, fun e1 e2 -> LocExpr.BExpr(e1, BOp.Add, e2)))
        opp.AddOperator(InfixOperator("-"   , spaces .>> notFollowedByString ">" , 4, Associativity.Left, fun e1 e2 -> LocExpr.BExpr(e1, BOp.Subtract, e2)))
        // >
        opp.AddOperator(InfixOperator("<="  , spaces , 3, Associativity.Left, fun e1 e2 -> LocExpr.BExpr(e1, BOp.LessEqual, e2)))
        opp.AddOperator(InfixOperator("=="  , spaces , 3, Associativity.Left, fun e1 e2 -> LocExpr.BExpr(e1, BOp.Equals, e2)))
        opp.AddOperator(InfixOperator("=/=" , spaces , 3, Associativity.Left, fun e1 e2 -> LocExpr.BExpr(e1, BOp.NotEquals, e2)))
        opp.AddOperator(InfixOperator(">="  , spaces , 3, Associativity.Left, fun e1 e2 -> LocExpr.BExpr(e1, BOp.GreaterEqual, e2)))
        opp.AddOperator(InfixOperator(">"   , spaces , 3, Associativity.Left, fun e1 e2 -> LocExpr.BExpr(e1, BOp.Greater, e2)))
        opp.AddOperator(InfixOperator("<"   , spaces , 3, Associativity.Left, fun e1 e2 -> LocExpr.BExpr(e1, BOp.Less, e2)))
        opp.AddOperator(PrefixOperator("!", spaces, 3, true, fun e -> LocExpr.UExpr(e,UOp.Not)))
        //>
        opp.AddOperator(InfixOperator("&&"   , spaces , 2, Associativity.Left, fun e1 e2 -> LocExpr.BExpr(e1, BOp.And, e2)))
        //>
        opp.AddOperator(InfixOperator("||"   , spaces , 1, Associativity.Left, fun e1 e2 -> LocExpr.BExpr(e1, BOp.Or, e2)))

        // parses an expression between ( and )
        let parenExpr_ws = between parentOpen_ws parentClose_ws (opp.ExpressionParser)
  

        // recursive term parser for expressions
        opp.TermParser <-
            (boolVal_ws |>> LocExpr.Literal) <|> 
            (numberVal_ws |>> LocExpr.Literal) <|>
            (attempt ((locatedFieldInst .>> notFollowedBy oldValueIndicator) .>> spaces) |>> LocExpr.ReadField) <|>
            (attempt ((locatedFaultInst .>> notFollowedBy oldValueIndicator) .>> spaces) |>> LocExpr.ReadFault) <|>
            (attempt ((locatedFieldInst .>> oldValueIndicator) .>> spaces) |>> LocExpr.ReadOldField) <|>
            (attempt ((locatedFaultInst .>> oldValueIndicator) .>> spaces) |>> LocExpr.ReadOldFault) <|>
            (attempt varIdInst_ws |>> LocExpr.ReadVar) <|> 
            (parenExpr_ws)
        opp.ExpressionParser

    let hierarchical_expression_ws = hierarchical_expression .>> spaces

    let typeBasic =
        let boolType = stringReturn "bool" Type.BoolType
        let intType = stringReturn "int" Type.IntType
        let realType = stringReturn "real" Type.RealType
        (boolType <|> intType <|> realType)
        
    let typeBasic_ws =
        typeBasic .>> spaces

    let typeBasic_ws1 =
        typeBasic .>> spaces1

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
    
    let varDeclInParam_ws : Parser<_,UserState> =
        let createVarDecl var _type =
            {
                VarDecl.Var = var ;
                VarDecl.Type = _type ;
            }
        pipe2 (varIdDecl_ws .>> (pstring_ws ":" )) 
              (typeBasic_ws)
              createVarDecl
              
    let paramDecl_ws : Parser<_,UserState> =
        let createParamDecl varDecl dir =
            {
                ParamDecl.Var = varDecl
                ParamDecl.Dir = dir ;
            }
        let inParam_ws =
            attempt ((pstring_ws1 "in") >>. varDeclInParam_ws) |>> (fun varDecl -> createParamDecl varDecl ParamDir.In)
        let inoutParam_ws =
            attempt ((pstring_ws1 "inout") >>. varDeclInParam_ws) |>> (fun varDecl -> createParamDecl varDecl ParamDir.InOut)
        inParam_ws <|> inoutParam_ws

    let paramDecls_ws =
        sepBy paramDecl_ws (pstring_ws ",")
    
    
    let varDeclLocal_ws : Parser<_,UserState> =
        let createVarDecl _type var=
            {
                VarDecl.Var = var ;
                VarDecl.Type = _type ;
            }
        pipe2 (typeBasic_ws1) //ws1 to ensure, that at least one space is available (thus "intx" is not valid. Need space between int and x)
              (varIdDecl_ws ) 
              createVarDecl

    let varDeclsLocal_ws =
        many (attempt (varDeclLocal_ws .>> (pstring_ws ";")))

    let behaviorDecl_ws  =
        let createBehavior locals body =
            {
                BehaviorDecl.Locals = locals ;
                BehaviorDecl.Body = body;
            }
        pipe2 (varDeclsLocal_ws)
              (many statement_ws |>> Stm.Block)
              createBehavior
    
    let faultExpr_ws  : Parser<_,UserState> =
        let opp = new OperatorPrecedenceParser<_,_,_>()
        opp.AddOperator(PrefixOperator("!", spaces, 3, true, fun e -> FaultExpr.NotFault(e)))
        //>
        opp.AddOperator(InfixOperator("&&"   , spaces , 2, Associativity.Left, fun e1 e2 -> FaultExpr.AndFault(e1,e2)))
        //>
        opp.AddOperator(InfixOperator("||"   , spaces , 1, Associativity.Left, fun e1 e2 -> FaultExpr.OrFault(e1,e2)))
        // parses an expression between ( and )
        let parenExpr_ws = between parentOpen_ws parentClose_ws (opp.ExpressionParser)        
        // recursive term parser for expressions
        opp.TermParser <-
            (faultIdInst_ws |>> FaultExpr.Fault) <|> 
            (parenExpr_ws)
        opp.ExpressionParser

    let faultExprOpt_ws =
        let foundSomething = (pstring_ws "[") >>. faultExpr_ws .>> (pstring_ws "]")
        ((attempt foundSomething) |>> Some) <|>
        (spaces >>% None)
     

    let contract_ws : Parser<_,UserState> =
        fun stream ->
            let createContract (requires:LocExpr option) (ensures:LocExpr option) (changed:string list option) =
                if requires.IsNone && ensures.IsNone && changed.IsNone then
                    Contract.None
                else
                    if changed.IsNone then
                        Contract.AutoDeriveChanges(requires,ensures)
                    else
                        let changedFields,changedFaults =
                            let rec transformChanged (changedFields:(Field list),changedFaults:(Fault list)) (changed:string list) : (Field list)*(Fault list)=
                                if changed.IsEmpty then
                                    changedFields,changedFaults
                                else
                                    let changedElement = changed.Head
                                    let changedFields =
                                        if stream.UserState.IsIdentifierOfType changedElement IdentifierType.Field then
                                            Field.Field(changedElement)::changedFields
                                        else
                                            changedFields
                                    let changedFaults =
                                        if stream.UserState.IsIdentifierOfType changedElement IdentifierType.Fault then
                                            Fault.Fault(changedElement)::changedFaults
                                        else
                                            changedFaults
                                    transformChanged (changedFields,changedFaults) changed.Tail
                            transformChanged ([],[]) changed.Value
                        Contract.Full(requires,ensures,changedFields,changedFaults)
            pipe3 (opt (pstring_ws1 "requires" >>. hierarchical_expression_ws) )
                  (opt (pstring_ws1 "ensures" >>. hierarchical_expression_ws) )
                  (opt (pstring_ws1 "changes" >>. sepBy parseIdentifier_ws (pstring_ws ",") ) )
                  createContract
                  stream

    let stepDecl =
        let createStep faultExpr contract behavior =
            {
                StepDecl.FaultExpr = faultExpr
                StepDecl.Behavior = behavior;
                StepDecl.Contract = contract
            }
        pipe3 (faultExprOpt_ws .>> (pstring_ws "step"))
              (contract_ws  .>> (pstring_ws "{") .>> pushUserStateCallStack)
              (behaviorDecl_ws .>> (pstring_ws "}") .>> popUserStateCallStack)
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
                       (typeExtended_ws .>> (pstring_ws "="))
                       ((sepBy1 value_ws (pstring_ws ",")) .>> (pstring_ws ";"))
                       createFieldDecl)

    let faultDecls_ws : Parser<_,UserState> =
        let createFaultDecl faultId behavior =
            {
                FaultDecl.Fault = faultId;
                FaultDecl.Step = behavior;
            }
        pipe2 ((pstring_ws1 "fault") >>. faultIdDecl_ws)
              ( (pstring_ws "{") >>. (pstring_ws "step") >>. (pstring_ws "{") >>. pushUserStateCallStack >>. behaviorDecl_ws .>> (pstring_ws "}") .>> popUserStateCallStack .>> (pstring_ws "}"))
              createFaultDecl

    let reqPortDecl_ws : Parser<_,UserState> =
        let createReqPortDecl name parms =
            {
                ReqPortDecl.ReqPort = name;
                ReqPortDecl.Params = parms ;
            }
        attempt (pipe2 (reqPortId_ws .>> parentOpen_ws .>> pushUserStateCallStack)
                       (paramDecls_ws .>> parentClose_ws .>> popUserStateCallStack .>> (pstring_ws ";"))
                       createReqPortDecl)

    let provPortDecl_ws : Parser<_,UserState> =
        let createProvPortDecl faultExpr name parms contract behavior =
            {
                ProvPortDecl.ProvPort = name;
                ProvPortDecl.Params = parms ;
                ProvPortDecl.Behavior = behavior;
                ProvPortDecl.FaultExpr = faultExpr;
                ProvPortDecl.Contract = contract
            }
        attempt (pipe5 (faultExprOpt_ws)
                       (provPortId_ws .>> parentOpen_ws .>> pushUserStateCallStack)
                       (paramDecls_ws .>> parentClose_ws)
                       (contract_ws .>> (pstring_ws "{"))
                       (behaviorDecl_ws .>> (pstring_ws "}") .>> popUserStateCallStack)
                       createProvPortDecl)
                              
    let binding_ws : Parser<_,UserState> =
        let bindingsrc_ws =
            let createProvPort (comps,srcPort) = {BndSrc.Comp = comps; BndSrc.ProvPort=srcPort}
            attempt (comppath_dot .>>. provPortId_ws) |>> createProvPort

        let bindingtarget_ws =
            let createReqPort (comps,targetPort) = {BndTarget.Comp = comps; BndTarget.ReqPort=targetPort}
            attempt (comppath_dot .>>. reqPortId_ws) |>> createReqPort
        
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
                    BndDecl.Kind = BndKind.Delayed;
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
                CompDecl.Faults = faults;
                CompDecl.ReqPorts = reqPorts;
                CompDecl.ProvPorts = provPorts;
                CompDecl.Bindings = bindings;
                CompDecl.Steps = steps;
            }
        pipe8 ((pstring_ws1 "component") >>. declareComponentName_and_pushUserStateComponentStack_ws .>> (pstring_ws "{"))
              (many comp_ws)
              (many typedFieldDecl_ws)
              (many faultDecls_ws)
              (many reqPortDecl_ws)
              (many provPortDecl_ws)
              (many binding_ws)
              ((many stepDecl_ws) .>> (pstring "}") .>> popUserStateComponentStack)
              createComponent
        
    let scmFile = comp_ws
    
    
    open SafetySharp.Workflow
    open SafetySharp.Models.ScmTracer
    
    let parseStringWorkflow () : ExogenousWorkflowFunction<string,ScmTracer.SimpleScmTracer<Scm.Traceable>> = workflow {
        
        let runWithUserState parser str = runParserOnString parser UserState.initialUserState "" str

        let parseWithParser parser str =
            match runWithUserState parser str with
            | Success(result, _, _)   -> result
            | Failure(errorMsg, a, b) -> failwith errorMsg
            
        let! model = SafetySharp.Workflow.getState ()
        let rootComp = parseWithParser (scmFile .>> eof) model
        let scmModel = ScmModel(rootComp)
        do! setInitialSimpleScmTracer scmModel
    }